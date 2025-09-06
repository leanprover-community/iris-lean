import os
import re

# Define the base directory for the paper
paper_dir = os.path.join(os.path.dirname(__file__), '..', 'paper')
main_paper_file = os.path.join(paper_dir, 'paper.tex')
sections_dir = os.path.join(paper_dir, 'section')

# A more robust mapping from keywords in section titles to filenames.
# The order is important: more specific keys should come before general ones.
section_title_to_filename_map = [
    ('Case Studies for \\thelogic', 'casestudies.tex'),
    ('A Tour of \\thelogic', 'overview.tex'),
    ('The Rules of \\thelogic', 'appendix_rules.tex'),
    ('Preliminaries', 'preliminaries.tex'),
    ('The \\thelogic\\ Logic', 'logic.tex'),
    ('Characterizations of \\SuperCond\\ and Relational Lifting', 'appendix_characterizations.tex'),
    ('Related Work', 'relatedwork.tex'),
    ('Conclusions and Future Work', 'conclusion.tex'),
    ('Introduction', 'introduction.tex'),
    ('Acknowledgments', 'acks.tex'),
    # Appendix sections
    ('Auxiliary Definitions', 'appendix_definitions.tex'),
    ('Measure Theory Lemmas', 'appendix_measure.tex'),
    ('Model', 'appendix_model.tex'),
    ('Soundness', 'appendix_soundness.tex'),
    ('Case Studies', 'appendix_case_studies.tex'), # General 'Case Studies' for appendix
    ('Derived Rules', 'appendix_rules.tex')
]

def get_filename_from_title(title):
    """Finds the corresponding filename from the section title using the ordered map."""
    for keyword, filename in section_title_to_filename_map:
        if keyword in title:
            return filename
    return None

def main():
    """Main splitting function."""
    written_files = set()
    print(f"Starting automatic split of {main_paper_file}...")

    try:
        with open(main_paper_file, 'r', encoding='utf-8') as f:
            content = f.read()
    except FileNotFoundError:
        print(f"[ERROR] Main paper file not found: {main_paper_file}")
        return

    # Regex to find all section commands and their titles
    section_regex = re.compile(r"\\section(?:\*)?\{(.*?)\}", re.DOTALL)
    matches = list(section_regex.finditer(content))

    if not matches:
        print("[ERROR] No \\section commands found in the paper. Cannot split.")
        return

    # Create the section directory if it doesn't exist
    os.makedirs(sections_dir, exist_ok=True)

    # Iterate through the sections and split the content
    for i, match in enumerate(matches):
        section_title = match.group(1)
        start_pos = match.start()
        
        # The end position is the start of the next section, or the end of the file
        end_pos = matches[i+1].start() if i + 1 < len(matches) else len(content)
        
        section_content = content[start_pos:end_pos].strip()
        
        filename = get_filename_from_title(section_title)
        
        if filename:
            output_path = os.path.join(sections_dir, filename)

            if output_path in written_files:
                write_mode = 'a'
            else:
                write_mode = 'w'
                written_files.add(output_path)

            print(f"  -> Writing section '{section_title}' to {output_path} (mode: {write_mode})")
            try:
                with open(output_path, write_mode, encoding='utf-8') as f_out:
                    f_out.write(section_content + '\n\n')
            except IOError as e:
                print(f"    [ERROR] Could not write to file: {e}")
        else:
            print(f"  [WARNING] No filename mapping for section: '{section_title}'. Skipping.")

    print("\nSplitting process complete.")
    print(f"Suggestion: Review the files in '{sections_dir}' to ensure correctness.")
    print("Then, update 'paper.tex' to use \\input{{...}} commands for each section.")

if __name__ == "__main__":
    main()
