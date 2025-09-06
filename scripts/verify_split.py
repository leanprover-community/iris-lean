import os
import difflib

# Define the base directory for the paper
paper_dir = os.path.join(os.path.dirname(__file__), '..', 'paper')
main_paper_file = os.path.join(paper_dir, 'paper.tex')
sections_dir = os.path.join(paper_dir, 'section')

# Define the logical order of sections
# This order is inferred from common paper structures.
section_files = [
    'introduction.tex',
    'overview.tex',
    'preliminaries.tex',
    'logic.tex',
    'casestudies.tex',
    'relatedwork.tex',
    'conclusion.tex',
    'acks.tex',
    'appendix_definitions.tex',
    'appendix_model.tex',
    'appendix_characterizations.tex',
    'appendix_rules.tex',
    'appendix_measure.tex',
    'appendix_soundness.tex',
    'appendix_case_studies.tex'
]

def find_best_match_and_diff(section_path, section_content, main_content):
    """Finds the best matching block in the main content and returns a diff."""
    section_lines = section_content.splitlines(keepends=True)
    main_lines = main_content.splitlines(keepends=True)

    # Use SequenceMatcher to find the best matching block
    s = difflib.SequenceMatcher(None, main_lines, section_lines, autojunk=False)
    match = s.find_longest_match(0, len(main_lines), 0, len(section_lines))

    if match.size == 0:
        return None, "No plausible match found."

    # Extract the corresponding blocks
    main_block = main_lines[match.a : match.a + match.size]
    section_block = section_lines[match.b : match.b + match.size]

    # Diff the matched blocks to see minor differences
    diff = list(difflib.unified_diff(main_block, section_block, fromfile='in_paper.tex', tofile='in_section_file.tex'))

    # Also diff the full section against a similarly sized chunk from the main file
    main_chunk_for_diff = main_lines[match.a : match.a + len(section_lines)]
    full_diff = list(difflib.unified_diff(main_chunk_for_diff, section_lines, fromfile='paper.tex (best guess)', tofile=os.path.basename(section_path)))

    return match, full_diff

def verify_section_in_main_paper(section_path, main_path):
    """Checks if the content of the section file is present in the main paper file."""
    try:
        with open(section_path, 'r', encoding='utf-8') as f_section:
            section_content = f_section.read()
    except FileNotFoundError:
        print(f"- Section file not found: {os.path.basename(section_path)}")
        return False, None

    if not section_content.strip():
        print(f"- Section file is empty: {os.path.basename(section_path)}")
        return True, None

    try:
        with open(main_path, 'r', encoding='utf-8') as f_main:
            main_content = f_main.read()
            if section_content in main_content:
                return True, None
            else:
                # If direct match fails, perform a diff
                match, diff = find_best_match_and_diff(section_path, section_content, main_content)
                if match:
                    similarity = match.size / len(section_content.splitlines(keepends=True))
                    return False, (similarity, diff)
                return False, (0, None)

    except FileNotFoundError:
        print(f"- Main paper file not found: {main_path}")
        return False, None
    except Exception as e:
        print(f"- Error reading main paper file: {e}")
        return False, None

def main():
    """Main verification function."""
    print(f"Starting verification of paper split...")
    print(f"Main paper: {main_paper_file}")
    print(f"Sections directory: {sections_dir}\n")

    all_found = True
    for section_filename in section_files:
        section_path = os.path.join(sections_dir, section_filename)
        print(f"Checking section: {section_filename}...")
        
        is_found, diff_info = verify_section_in_main_paper(section_path, main_paper_file)

        if is_found:
            print(f"  [OK] Content of '{section_filename}' found in the main paper.\n")
        else:
            all_found = False
            if diff_info:
                similarity, diff = diff_info
                print(f"  [MISMATCH] Content of '{section_filename}' NOT found directly.")
                print(f"  Best match similarity: {similarity:.2%}")
                if diff:
                    print("  Showing differences (limit 20 lines):")
                    for line in diff[:20]:
                        print(f"    {line.strip()}")
                    if len(diff) > 20:
                        print("    ... (diff truncated)")
                else:
                    print("  Could not generate a meaningful diff.")
            else:
                print(f"  [ERROR] Could not process section '{section_filename}'.")
            print()

    print("----------------------------------------")
    if all_found:
        print("Verification successful: All section files are fully contained in paper.tex.")
        print("Suggestion: You can now replace the content in paper.tex with \\input commands.")
    else:
        print("Verification failed: One or more sections did not match.")
        print("Suggestion: Review the mismatched files. There may be differences in content or encoding.")

if __name__ == "__main__":
    main()
