import os
import re

# Define the base directory for the paper
sections_dir = os.path.join(os.path.dirname(__file__), '..', 'paper', 'section')

def analyze_file(filepath):
    """Analyzes a single .tex file for line count and subsection structure."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except FileNotFoundError:
        return None

    total_lines = len(lines)

    # Find all subsection and subsubsection commands and their line numbers
    section_regex = re.compile(r'\\(sub)*section\*?\{(.*?)\}')
    sections = []
    for i, line in enumerate(lines):
        match = section_regex.search(line)
        if match:
            # We only care about subsections and subsubsections within a file
            if 'subsection' in match.group(0) or 'subsubsection' in match.group(0):
                sections.append({
                    'title': match.group(2).strip(),
                    'line': i + 1,
                    'type': match.group(0).split('{')[0]
                })

    # Calculate lengths
    for i, sec in enumerate(sections):
        next_sec_line = total_lines + 1
        # Find the next section/subsection to determine the end
        for j in range(i + 1, len(sections)):
            next_sec_line = sections[j]['line']
            break
        sec['length'] = next_sec_line - sec['line']

    return {'total_lines': total_lines, 'subsections': sections}

def main():
    """Main analysis function."""
    print("Analyzing section files...\n")
    
    all_files_data = []
    try:
        section_filenames = [f for f in os.listdir(sections_dir) if f.endswith('.tex')]
    except FileNotFoundError:
        print(f"[ERROR] Sections directory not found: {sections_dir}")
        return

    for filename in section_filenames:
        filepath = os.path.join(sections_dir, filename)
        analysis = analyze_file(filepath)
        if analysis:
            all_files_data.append({'filename': filename, **analysis})

    # Sort files by line count, descending
    all_files_data.sort(key=lambda x: x['total_lines'], reverse=True)

    print("--- Section Line Counts ---")
    for data in all_files_data:
        print(f"{data['filename']}: {data['total_lines']} lines")

    print("\n--- Analysis of Longest Sections ---")
    # Report on the top 5 longest files
    for data in all_files_data[:5]:
        print(f"\nFile: {data['filename']} (Total Lines: {data['total_lines']})")
        if data['subsections']:
            for sub in data['subsections']:
                indent = "  " if sub['type'] == '\\subsection' else "    "
                print(f"{indent}{sub['type']}: {sub['title']} (~{sub['length']} lines)")
        else:
            print("  No subsections found.")

if __name__ == "__main__":
    main()
