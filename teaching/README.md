# Teaching pages

This repository serves static HTML directly. No build step is required.

- `/teaching/`: course selection.
- `/teaching/advanced-topics-data-analytics/`: Advanced Topics in Data Analytics, Group 2.
- `/teaching/software-engineering/`: Software Engineering template.

Edit each course's `index.html` to replace TBA values and add lecture rows.
The shared styling is in `/css/main.css`.
Keep the navigation consistent across the homepage and these three pages.

The first meeting's slides remain TBA until the presentation is final.
Instructions for adding them are in the course's `slides/README.md`.

To preview from the repository root:

```bash
python3 -m http.server 8000
```

Open `http://localhost:8000/` and follow Teaching in the navigation.
