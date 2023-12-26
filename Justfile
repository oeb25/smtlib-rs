# CI/Release

release-patch args="":
    # git checkout HEAD -- CHANGELOG.md
    cargo release patch {{args}}

release-hook:
    git cliff -t $NEW_VERSION -o CHANGELOG.md
