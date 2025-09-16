#!/bin/bash

# This script finds `sorry` statements and creates focused GitHub issues.
# It now ignores any `sorry` found inside a single-line comment (`--`).

set -e

# --- 📝 User Configuration ---
# The script will read your API key from this environment variable.
GEMINI_API_KEY="${GEMINI_API_KEY:-}"
ISSUE_LABEL="proof wanted"

# --- Function Definitions ---

# Calls the Gemini API to summarize a Lean code snippet.
# $1: The code snippet to be summarized.
generate_summary() {
  local code_snippet="$1"
  
  # Silently skip if the API key is not set or jq is not installed.
  if [[ -z "$GEMINI_API_KEY" ]] || ! command -v jq &> /dev/null; then
    echo ""
    return
  fi

  local prompt="In one sentence, explain the goal of the following Lean 4 declaration. Do not include the words 'the user' or 'the goal is'. For example, for 'theorem two_plus_two : 2 + 2 = 4', respond with 'This theorem proves that 2 + 2 equals 4.'. Here is the code:\n\n\`\`\`lean\n$code_snippet\n\`\`\`"

  # Use jq to safely construct the JSON payload.
  local json_payload
  json_payload=$(jq -n --arg prompt "$prompt" \
    '{contents: [{parts: [{text: $prompt}]}]}')

  # Make the API call and parse the response.
  local response
  response=$(curl --fail -s -H "Content-Type: application/json" \
    -d "$json_payload" \
    "https://generativelanguage.googleapis.com/v1beta/models/gemini-pro:generateContent?key=$GEMINI_API_KEY" 2>/dev/null) || true
  
  # Extract the text content, providing an empty string on failure.
  echo "$response" | jq -r '.candidates[0].content.parts[0].text // ""'
}

# Template for the issue title.
generate_issue_title() {
  local file_path="$1"
  local decl_name="$2"
  local line_num="$3"

  if [[ -z "$decl_name" ]]; then
    echo "Proof obligation in \`$file_path\` near line $line_num"
  else
    echo "Proof obligation for \`$decl_name\` in \`$file_path\`"
  fi
}

# Template for the issue body.
generate_issue_body() {
  local file_path="$1"
  local sorry_line_num="$2"
  local repo_name="$3"
  local full_code_snippet="$4"
  local ai_summary="$5" # New argument for the AI summary

  # Prepare the AI summary section, only if the summary is not empty.
  local summary_section=""
  if [[ -n "$ai_summary" ]]; then
    summary_section=$(cat <<EOF

**🤖 AI Summary:**
> $ai_summary
EOF
    )
  fi

  cat <<EOF
A proof in \`$file_path\` contains a \`sorry\`.
$summary_section

**Goal:** Replace the \`sorry\` with a complete proof.

[Link to the sorry on GitHub](https://github.com/$repo_name/blob/master/$file_path#L$sorry_line_num)

**Code Snippet:**
\`\`\`lean
$full_code_snippet
\`\`\`
EOF
}

# --- Script Logic ---
SEARCH_PATH="${1:-.}"
if [ ! -d "$SEARCH_PATH" ]; then
  echo "❌ Error: Directory '$SEARCH_PATH' not found."
  exit 1
fi

GIT_ROOT=$(git rev-parse --show-toplevel)
cd "$GIT_ROOT"

REPO=$(gh repo view --json nameWithOwner --jq .nameWithOwner)
if [ -z "$REPO" ]; then
    echo "❌ Error: Could not determine GitHub repository."
    exit 1
fi
echo "✅ Detected repository: $REPO"
echo "🔎 Scanning for 'sorry' statements in '$SEARCH_PATH'..."
echo "----------------------------------------------------"

AWK_SCRIPT='
FNR == 1 { current_decl_header = ""; current_decl_linenum = 0; }
/^(private|protected)?[ \t]*(noncomputable)?[ \t]*(theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)[ \t]+/ {
    header = $0; sub(/--.*/, "", header); sub(/[ \t]*$/, "", header);
    sub(/[ \t]*where$/, "", header); sub(/[ \t]*:=$/, "", header);
    current_decl_header = header; current_decl_linenum = FNR;
}
/sorry/ {
    comment_pos = index($0, "--"); sorry_pos = index($0, "sorry");
    if (comment_pos == 0 || sorry_pos < comment_pos) {
        print FILENAME "|" FNR "|" current_decl_linenum "|" current_decl_header "|" $0
    }
}
'

find "$SEARCH_PATH" -name "*.lean" -type f -not -path "*/.lake/*" -not -path "*/build/*" \
  | xargs awk "$AWK_SCRIPT" | while IFS='|' read -r FILE SORRY_LINE_NUM DECL_START_LINE DECL_HEADER SORRY_CODE; do
    
    DECL_HEADER=$(echo "$DECL_HEADER" | xargs)
    DECL_NAME_ONLY=$(echo "$DECL_HEADER" | sed -E 's/.*(theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)[ \t]+([^\s\(\{:]+).*/\2/')
    
    if [ "$DECL_START_LINE" -eq 0 ]; then DECL_START_LINE=$SORRY_LINE_NUM; fi
    FULL_SNIPPET=$(sed -n "${DECL_START_LINE},${SORRY_LINE_NUM}p" "$FILE")
    
    echo "🤖 Calling Gemini API for summary of '$DECL_NAME_ONLY'..."
    AI_SUMMARY=$(generate_summary "$FULL_SNIPPET")
    
    # FIXED: Changed "$file" to "$FILE" to match the correct variable.
    TITLE=$(generate_issue_title "$FILE" "$DECL_NAME_ONLY" "$SORRY_LINE_NUM")
    BODY=$(generate_issue_body "$FILE" "$SORRY_LINE_NUM" "$REPO" "$FULL_SNIPPET" "$AI_SUMMARY")

    echo "✅ Creating issue for '$DECL_NAME_ONLY' in $FILE"
    gh issue create \
      --title "$TITLE" \
      --body "$BODY" \
      --label "$ISSUE_LABEL"

done

echo "----------------------------------------------------"
echo "🎉 All done! Named issues have been created."