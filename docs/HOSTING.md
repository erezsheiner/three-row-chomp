# Hosting this release

This is a static website package. Its search page, individual result pages and local proof attachments can be served without a database. Preparing the release does not create a public repository or deploy it.

## Check the selected package

Use the isolated release directory. Its `PUBLICATION-STATUS.json` and `audit/release/REVIEW.json` must approve the scoped release, and the current files must match `audit/release/INPUTS.json` and `audit/release/RELEASE-FILES.json`. Run the release's supplied gate and technical validation before packaging or deploying it.

The original full-collection directory remains on HOLD and is not the publication source. Do not copy it wholesale or change its status to release this subset. The excluded open and unresolved claims must stay absent from the public result catalogue.

To inspect the already built site locally, run from the release root:

```text
python -m http.server 8000 --directory site/dist
```

Then open `http://localhost:8000/`. Check the search, individual result pages, proof attachments and Lean source downloads. Each conditional result should retain its assumptions in its public page.

## Public deployment

Deploy only the sealed website archive or an exact allowlist export to GitHub Pages or another static host. A public source repository should contain only the release files admitted by the allowlist. The release's gate must remain part of the deployment process; successful hosting does not add mathematical approval. To produce a fresh deployment directory, run:

```text
python scripts/export_approved_site.py --destination ../three-row-chomp-approved-site
```

The destination must not already exist. The exporter checks approval, copies only the website manifest's files and the two fixed approval envelopes, and verifies every exported file hash. Extra files in `site/dist/` are not included.

The sealed website works with relative links, including under a GitHub Pages repository path. To add address-specific canonical links and a sitemap, configure the final base address, including any repository path such as `https://OWNER.github.io/REPOSITORY/`, before preparing a new release. Rebuilding changes the approved bytes: repeat the relevant display and link checks, update the review bindings and reseal the release before deployment. The deployment workflow does not rebuild or alter approved pages.

The GitHub Pages workflow uploads only a fresh verified allowlist export from this release. Running that deployment or uploading to another host is a separate external action; it has not been performed by preparing the package.

## Search visibility and citation

Individual static result pages provide the text and stable links that search engines can index. Public hosting and a sitemap make those pages available to crawlers; they do not guarantee indexing, ranking or a particular discovery time.

Use the exact result title, statement and hypotheses when linking or citing a page. The paper results and Lean declarations are distinct evidence layers. A future note or article revision can link to a stable release URL, but this package does not submit or revise any arXiv article.

Any later source or catalogue change should pass the relevant review and receive updated release hashes before a replacement deployment. Preserve the versioned edition so citations continue to identify the evidence that was actually reviewed.

## GitHub Pages workflow

Upload the repository ZIP contents to a public GitHub repository. In Settings → Pages, choose GitHub Actions. Then run the included **Publish research library to GitHub Pages** workflow manually. It checks the scoped gate, exports the exact approved website into a fresh runner directory, verifies its allowlist and hashes, and uploads only that directory. It does not rebuild after approval or upload unlisted pages. No placeholder public URL is embedded in this package. The standalone website ZIP is already crawlable with relative links and can also be uploaded directly to a static host.

The workflow follows the official [Pages artifact action](https://github.com/actions/upload-pages-artifact); the formal CI uses the official [Lean action](https://github.com/leanprover/lean-action). Cloud workflows have been prepared and inspected locally; they have not run on GitHub yet.
