import os
import sys
import subprocess
import re
import argparse
import google.generativeai as genai

# --- ⚙️ Configuration ---
ISSUE_LABEL = "proof-wanted"

# --- Helper Functions ---

def run_command(command):
    """Runs a command and returns its stdout, exiting on failure."""
    try:
        result = subprocess.run(
            command, check=True, capture_output=True, text=True, encoding='utf-8'
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"❌ Error running command: {' '.join(command)}\n{e.stderr}", file=sys.stderr)
        sys.exit(1)

def generate_ai_analysis(code_snippet: str, full_file_content: str) -> str:
    """Calls the Gemini API to generate a detailed analysis of a proof obligation."""
    print(f"🤖 Calling Gemini API for detailed analysis...")
    try:
        # The Gemini library automatically finds credentials from gcloud (ADC)
        model = genai.GenerativeModel('gemini-pro')
        
        prompt = (
            "You are an expert in Lean 4 and formal mathematics. Your task is to help a user by providing a detailed "
            "comment for a proof obligation marked with `sorry`.\n\n"
            "I will provide you with the full content of a Lean file and the specific declaration that needs to be proven.\n\n"
            "Your response must be a markdown-formatted comment with exactly three sections:\n"
            "1. `### Statement Explanation`: Explain what the theorem/definition states in clear terms.\n"
            "2. `### Context`: Explain how this statement relates to other definitions or theorems in the file. For example, mention if it's a key lemma for a larger proof or if it generalizes another concept in the file.\n"
            "3. `### Proof Suggestion`: Provide a high-level suggestion for how to approach the proof. You can mention relevant tactics or lemmas from the provided file content that might be useful.\n\n"
            "---\n\n"
            f"**Full File Content:**\n```lean\n{full_file_content}\n```\n\n"
            f"**Declaration with `sorry`:**\n```lean\n{code_snippet}\n```"
        )
        
        response = model.generate_content(prompt)
        return response.text.strip()
    except Exception as e:
        print(
            f"⚠️ Warning: Gemini API call failed. Have you run 'gcloud auth application-default login'?",
            f"\n   Error: {e}",
            file=sys.stderr
        )
        return ""

def create_github_issue(title: str, body: str):
    """Uses the GitHub CLI to create an issue."""
    command = [
        "gh", "issue", "create",
        "--title", title,
        "--body", body,
        "--label", ISSUE_LABEL
    ]
    try:
        subprocess.run(command, check=True, capture_output=True, text=True, encoding='utf-8')
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to create GitHub issue.\nTitle: {title}\nError: {e.stderr}", file=sys.stderr)

# --- Main Logic ---

def main():
    parser = argparse.ArgumentParser(
        description="Find 'sorry' statements in a Lean project and create GitHub issues."
    )
    parser.add_argument(
        "search_path",
        nargs="?",
        default=".",
        help="The directory to scan for .lean files (defaults to the current directory)."
    )
    args = parser.parse_args()

    git_root = run_command(["git", "rev-parse", "--show-toplevel"])
    os.chdir(git_root)
    
    repo_name = run_command(["gh", "repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner"])
    
    decl_regex = re.compile(
        r"^(private|protected)?\s*(noncomputable)?\s*"
        r"(theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)\s+"
    )
    name_extract_regex = re.compile(
        r".*?(?:theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)\s+"
        r"([^\s\(\{:]+)"
    )
    
    print(f"✅ Detected repository: {repo_name}")
    print(f"🔎 Scanning for 'sorry' statements in '{args.search_path}'...")
    print("----------------------------------------------------")

    for root, dirs, files in os.walk(args.search_path):
        dirs[:] = [d for d in dirs if d not in ['.lake', 'build']]
        
        for file in sorted(files):
            if not file.endswith(".lean"):
                continue

            file_path = os.path.join(root, file)
            current_decl_header = ""
            current_decl_linenum = 0

            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            full_file_content = "".join(lines)

            for i, line in enumerate(lines):
                line_num = i + 1
                
                if decl_regex.search(line):
                    current_decl_header = line.strip()
                    current_decl_linenum = line_num

                if "sorry" in line:
                    comment_pos = line.find("--")
                    sorry_pos = line.find("sorry")
                    if comment_pos != -1 and sorry_pos > comment_pos:
                        continue

                    decl_name_match = name_extract_regex.match(current_decl_header)
                    decl_name_only = decl_name_match.group(1) if decl_name_match else ""

                    start_line = current_decl_linenum if current_decl_linenum > 0 else line_num
                    full_snippet = "".join(lines[start_line - 1 : line_num])

                    ai_analysis = generate_ai_analysis(full_snippet, full_file_content)

                    title = f"Proof obligation for `{decl_name_only}` in `{file_path}`"
                    if not decl_name_only:
                        title = f"Proof obligation in `{file_path}` near line {line_num}"

                    analysis_section = ""
                    if ai_analysis:
                        analysis_section = f"\n\n**🤖 AI Analysis:**\n{ai_analysis}"

                    body = (
                        f"A proof in `{file_path}` contains a `sorry`.\n{analysis_section}\n\n"
                        f"**Goal:** Replace the `sorry` with a complete proof.\n\n"
                        f"[Link to the sorry on GitHub](https://github.com/{repo_name}/blob/master/{file_path}#L{line_num})\n\n"
                        f"**Code Snippet:**\n```lean\n{full_snippet}\n```"
                    )
                    
                    print(f"✅ Creating issue for '{decl_name_only or 'task'}' in {file_path}")
                    create_github_issue(title, body)

    print("----------------------------------------------------")
    print("🎉 All done! Named issues have been created.")

if __name__ == "__main__":
    main()
