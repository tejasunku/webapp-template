# Justfile for Teja Pattern Web App Template
# Simple command runner for WSL compatibility

# Development commands
install:
    pnpm install

dev:
    pnpm run dev

# Formal verification tools
setup-formal-tools:
    #!/usr/bin/env sh
    echo "=== Setting up formal verification tools ==="
    echo ""
    echo "Checking for existing Java installation..."
    if command -v java >/dev/null 2>&1; then
        echo "✅ Java is already installed: $(java -version 2>&1 | head -1)"
        java_check=true
    else
        echo "❌ Java not found"
        java_check=false
    fi

    echo ""
    echo "Checking for existing Alloy installation..."
    if command -v alloy >/dev/null 2>&1; then
        echo "✅ Alloy is already installed: $(alloy version 2>/dev/null || echo 'version unknown')"
        alloy_check=true
    else
        echo "❌ Alloy not found"
        alloy_check=false
    fi

    echo ""
    if [ "$java_check" = true ] && [ "$alloy_check" = true ]; then
        echo "🎉 All formal verification tools are already installed!"
        echo "You can run: just alloy-verify"
    else
        echo "⚠️  Some tools need installation."
        echo ""
        echo "Choose installation method:"
        echo "1) just setup-formal-tools-global    # Install to user directory (~/.local)"
        echo "2) just setup-formal-tools-local     # Install to project directory (./tools)"
        echo ""
        echo "Recommendation: Use 'local' for project isolation."
    fi

setup-formal-tools-global:
    #!/usr/bin/env sh
    echo "=== Installing formal verification tools globally ==="
    echo "📦 Installing Java (OpenJDK 17) to user directory..."
    mkdir -p ~/.local/bin ~/.local/lib

    if ! command -v java >/dev/null 2>&1; then
        echo "Detecting platform..."
        if [ "$(uname)" = "Darwin" ]; then
            echo "macOS detected - using Homebrew..."
            if command -v brew >/dev/null 2>&1; then
                brew install openjdk@17
            else
                echo "Please install Java manually or install Homebrew first"
                echo "Visit: https://adoptium.net/"
                exit 1
            fi
        else
            echo "Linux detected - checking for apt..."
            if command -v apt >/dev/null 2>&1; then
                echo "Running: sudo apt update && sudo apt install -y openjdk-17-jdk"
                echo "You'll need to enter your password..."
                sudo apt update && sudo apt install -y openjdk-17-jdk
            else
                echo "Downloading OpenJDK 17..."
                cd /tmp
                wget -q https://download.oracle.com/java/17/latest/jdk-17_linux-x64_bin.tar.gz
                tar -xzf jdk-17_linux-x64_bin.tar.gz
                mv jdk-17.* ~/.local/lib/jdk-17
                rm jdk-17_linux-x64_bin.tar.gz
                echo 'export PATH="$HOME/.local/lib/jdk-17/bin:$PATH"' >> ~/.bashrc
                echo 'export JAVA_HOME="$HOME/.local/lib/jdk-17"' >> ~/.bashrc
                echo "Run 'source ~/.bashrc' or restart terminal to update PATH"
            fi
        fi
    fi
    echo "✅ Java installation completed"

    echo ""
    echo "📦 Installing Alloy Analyzer..."
    if ! command -v alloy >/dev/null 2>&1; then
        echo "Downloading Alloy Analyzer 5.0.0..."
        mkdir -p ~/.local/lib/alloy
        cd /tmp
        wget -q https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v5.0.0/alloy5.0.0.jar
        cp alloy5.0.0.jar ~/.local/lib/alloy/
        rm alloy5.0.0.jar

        echo '#!/bin/sh' > ~/.local/bin/alloy
        echo 'java -jar "$HOME/.local/lib/alloy/alloy5.0.0.jar" "$@"' >> ~/.local/bin/alloy
        chmod +x ~/.local/bin/alloy
        echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc 2>/dev/null || true
    fi
    echo "✅ Alloy installation completed"

    echo ""
    echo "🎉 Formal verification tools installed globally!"
    echo "Run 'source ~/.bashrc' or restart your terminal to update PATH"
    echo "Then run: just alloy-verify"

setup-formal-tools-system:
    #!/usr/bin/env sh
    echo "=== Installing formal verification tools via system packages ==="
    echo "📦 Installing Java (OpenJDK 17) via system package manager..."

    if command -v java >/dev/null 2>&1; then
        echo "✅ Java is already installed: $(java -version 2>&1 | head -1)"
    else
        echo "Installing Java via apt (you'll need to enter password)..."
        sudo apt update
        sudo apt install -y openjdk-17-jdk
        echo "✅ Java installed via system packages"
    fi

    echo ""
    echo "📦 Installing Alloy Analyzer..."
    mkdir -p tools/lib tools/bin

    # Try different download sources for Alloy
    echo "Attempting to download Alloy Analyzer 5.0.0..."
    cd /tmp

    # Try GitHub releases first
    if wget -q https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v5.0.0/alloy5.0.0.jar 2>/dev/null; then
        echo "✅ Downloaded from GitHub releases"
        cp alloy5.0.0.jar tools/lib/alloy5.0.0.jar
        rm alloy5.0.0.jar
    elif wget -q https://alloytools.org/alloy5.0.0.jar 2>/dev/null; then
        echo "✅ Downloaded from official site"
        cp alloy5.0.0.jar tools/lib/alloy5.0.0.jar
        rm alloy5.0.0.jar
    else
        echo "❌ Could not download Alloy. Please download manually:"
        echo "1. Visit: https://alloytools.org/"
        echo "2. Download alloy5.0.0.jar"
        echo "3. Place it in tools/lib/alloy5.0.0.jar"
        exit 1
    fi

    # Create alloy launcher script
    echo '#!/bin/sh' > tools/bin/alloy
    echo 'java -jar "$(dirname "$0")/../lib/alloy5.0.0.jar" "$@"' >> tools/bin/alloy
    chmod +x tools/bin/alloy

    echo "✅ Alloy installation completed"
    echo ""
    echo "🎉 Formal verification tools installed!"
    echo "Use ./tools/bin/alloy to run Alloy Analyzer"
    echo "Or run: just alloy-verify"

setup-formal-tools-local:
    #!/usr/bin/env sh
    # Get the justfile directory (project root)
    PROJECT_ROOT="$(dirname "$(readlink -f "${JUSTFILE:-justfile}")"
    echo "=== Installing formal verification tools locally ==="
    echo "Project root: $PROJECT_ROOT"
    cd "$PROJECT_ROOT" || exit 1

    mkdir -p tools/bin tools/lib

    echo "📦 Installing Java (OpenJDK 17) to ./tools..."
    if [ ! -f "tools/lib/jdk-17/bin/java" ]; then
        echo "Downloading OpenJDK 17..."
        DOWNLOAD_DIR="$PROJECT_ROOT/downloads"
        mkdir -p "$DOWNLOAD_DIR"
        cd "$DOWNLOAD_DIR"

        # Try different sources for Java
        if [ "$(uname)" = "Darwin" ]; then
            echo "macOS detected - using Homebrew..."
            if command -v brew >/dev/null 2>&1; then
                brew install --prefix="$PROJECT_ROOT/tools" openjdk@17
            else
                echo "Downloading OpenJDK 17 for macOS..."
                curl -L -o openjdk-17_macos.tar.gz "https://github.com/adoptium/temurin17-binaries/releases/download/jdk-17.0.12%2B7/OpenJDK17U-jdk_x64_mac_hotspot_17.0.12_7.tar.gz"
                tar -xzf openjdk-17_macos.tar.gz
                mv jdk-17.0.12+7-jdk "$PROJECT_ROOT/tools/lib/jdk-17"
                rm openjdk-17_macos.tar.gz
            fi
        else
            echo "Linux detected - downloading OpenJDK 17..."
            # Use Adoptium (Eclipse Temurin) which has more reliable URLs
            curl -L -o openjdk-17_linux.tar.gz "https://github.com/adoptium/temurin17-binaries/releases/download/jdk-17.0.12%2B7/OpenJDK17U-jdk_x64_linux_hotspot_17.0.12_7.tar.gz"
            tar -xzf openjdk-17_linux.tar.gz
            # Find the actual extracted directory name and move it
            if [ -d "jdk-17.0.12+7" ]; then
                mv jdk-17.0.12+7 "$PROJECT_ROOT/tools/lib/jdk-17"
            elif [ -d "jdk-17.0.12+7-jdk" ]; then
                mv jdk-17.0.12+7-jdk "$PROJECT_ROOT/tools/lib/jdk-17"
            else
                # Find any directory matching the pattern
                jdk_dir=$(ls -d jdk-17* 2>/dev/null | head -1)
                if [ -n "$jdk_dir" ]; then
                    mv "$jdk_dir" "$PROJECT_ROOT/tools/lib/jdk-17"
                else
                    echo "❌ Could not find extracted Java directory"
                    ls -la | grep jdk || true
                fi
            fi
            rm openjdk-17_linux.tar.gz
        fi

        # Return to project root
        cd "$PROJECT_ROOT"
    fi

    if [ -f "tools/lib/jdk-17/bin/java" ]; then
        echo "✅ Java installed to ./tools/lib/jdk-17"
        tools/lib/jdk-17/bin/java -version 2>&1 | head -1
    else
        echo "❌ Java installation failed"
        echo "You can install Java manually or use: just setup-formal-tools-system"
    fi

    echo ""
    echo "📦 Installing Alloy Analyzer (building from source)..."
    cd "$DOWNLOAD_DIR"

    # Clone and build Alloy from source (official method)
    if [ ! -d "org.alloytools.alloy" ]; then
        echo "Cloning Alloy repository..."
        git clone --recursive https://github.com/AlloyTools/org.alloytools.alloy.git
    else
        echo "Alloy repository already exists, updating..."
        cd org.alloytools.alloy
        git pull
        cd ..
    fi

    cd org.alloytools.alloy
    echo "Building Alloy with Gradle..."
    if command -v ./gradlew >/dev/null 2>&1; then
        # Set JAVA_HOME for our local Java installation
        export JAVA_HOME="$PROJECT_ROOT/tools/lib/jdk-17"
        export PATH="$JAVA_HOME/bin:$PATH"
        ./gradlew build
    else
        echo "❌ Gradle not found. Installing..."
        if command -v apt >/dev/null 2>&1; then
            echo "Installing Gradle via apt..."
            echo "You'll need to enter your password for this step."
            sudo apt update && sudo apt install -y gradle
            # Set JAVA_HOME for our local Java installation
            export JAVA_HOME="$PROJECT_ROOT/tools/lib/jdk-17"
            export PATH="$JAVA_HOME/bin:$PATH"
            ./gradlew build
        else
            echo "Please install Gradle manually and try again"
            exit 1
        fi
    fi

    # Move the entire Alloy directory to tools for future use
    echo "Moving Alloy installation to tools directory..."
    cd "$PROJECT_ROOT"
    if [ -d "$DOWNLOAD_DIR/org.alloytools.alloy" ]; then
        mv "$DOWNLOAD_DIR/org.alloytools.alloy" "tools/"
        echo "✅ Alloy source moved to ./tools/org.alloytools.alloy"
    else
        echo "❌ Could not find built Alloy directory"
        exit 1
    fi

    # Copy the built jar to tools directory
    if [ -f "tools/org.alloytools.alloy/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar" ]; then
        mkdir -p "tools/lib"
        cp tools/org.alloytools.alloy/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar "tools/lib/alloy.jar"
        echo "✅ Alloy jar copied to tools/lib/alloy.jar"
    else
        echo "❌ Build failed - could not find alloy.jar"
        ls -la tools/org.alloytools.alloy/org.alloytools.alloy.dist/target/ || true
        exit 1
    fi

    # Create alloy launcher script (ensure directories exist)
    mkdir -p tools/bin

    # Check for the built jar
    if [ -f "tools/lib/alloy.jar" ]; then
        echo '#!/bin/sh' > tools/bin/alloy
        if [ -f "tools/lib/jdk-17/bin/java" ]; then
            echo 'DIR="$(cd "$(dirname "$0")" && pwd)"' >> tools/bin/alloy
            echo 'JAVA_HOME="$DIR/../lib/jdk-17"' >> tools/bin/alloy
            echo '"$JAVA_HOME/bin/java" -jar "$DIR/../lib/alloy.jar" "$@"' >> tools/bin/alloy
        else
            echo 'java -jar "$(dirname "$0")/../lib/alloy.jar" "$@"' >> tools/bin/alloy
        fi
        chmod +x tools/bin/alloy
        echo "✅ Alloy installed to ./tools/lib/alloy.jar (built from source)"
    fi

    echo ""
    echo "📦 Installing TLA+ Toolbox..."
    cd "$DOWNLOAD_DIR"

    # Download TLA+ Toolbox (includes TLA+ tools and TLC model checker)
    if [ ! -f "tla2tools.jar" ]; then
        echo "Downloading TLA+ Toolbox..."
        # Use the latest stable TLA+ tools release
        curl -L -o tla2tools.jar "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
    fi

    # Create TLA+ executable script using echo commands
    mkdir -p "$PROJECT_ROOT/tools/bin"
    echo '#!/bin/bash' > "$PROJECT_ROOT/tools/bin/tlc"
    echo '# Get the directory where this script is located' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo 'SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo 'PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo '' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo '# Use local Java if available, otherwise system Java' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo 'if [ -f "$PROJECT_ROOT/lib/jdk-17/bin/java" ]; then' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo '    JAVA_CMD="$PROJECT_ROOT/lib/jdk-17/bin/java"' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo 'else' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo '    JAVA_CMD="java"' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo 'fi' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo '' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo '# Run TLA+ model checker' >> "$PROJECT_ROOT/tools/bin/tlc"
    echo 'exec "$JAVA_CMD" -cp "$SCRIPT_DIR/../lib/tla2tools.jar" tlc2.TLC "$@"' >> "$PROJECT_ROOT/tools/bin/tlc"

    # Make TLA+ scripts executable
    chmod +x "$PROJECT_ROOT/tools/bin/tlc"

    # Copy TLA+ tools jar to lib directory
    mkdir -p "$PROJECT_ROOT/tools/lib"
    cp "$DOWNLOAD_DIR/tla2tools.jar" "$PROJECT_ROOT/tools/lib/"

    # Return to project root
    cd "$PROJECT_ROOT"

    echo ""
    echo "🎉 Local installation completed!"
    if [ -f "tools/lib/jdk-17/bin/java" ]; then
        echo "Java: $(tools/lib/jdk-17/bin/java -version 2>&1 | head -1)"
    else
        echo "Java: Use system Java"
    fi
    if [ -f "tools/bin/alloy" ]; then
        echo "Alloy: ./tools/bin/alloy (built from source)"
    else
        echo "Alloy: Use system or install manually"
    fi
    if [ -f "tools/bin/tlc" ]; then
        echo "TLA+: ./tools/bin/tlc (v1.8.0)"
    else
        echo "TLA+: Use system or install manually"
    fi
    echo ""
    echo "Run: just alloy-verify or just tla-verify"

alloy-verify:
    #!/usr/bin/env sh
    echo "=== Running Alloy formal verification ==="

    # Get the justfile directory (project root)
    PROJECT_ROOT="$(dirname "$(readlink -f "${JUSTFILE:-justfile}")")"
    cd "$PROJECT_ROOT" || exit 1

    if [ -f "tools/bin/alloy" ]; then
        ALLOY_CMD="./tools/bin/alloy"
        JAVA_CMD="tools/lib/jdk-17/bin/java"
    elif command -v alloy >/dev/null 2>&1; then
        ALLOY_CMD="alloy"
        JAVA_CMD="java"
    else
        echo "❌ Alloy not found. Please run: just setup-formal-tools"
        exit 1
    fi

    echo "🔍 Using Alloy: $ALLOY_CMD"
    echo "📁 Analyzing model: docs/architecture/v0.0/alloy/client-factory.als"
    echo ""
    echo "Running verification checks..."

    # Create output directory
    mkdir -p docs/architecture/v0.0/alloy/results

    # Run Alloy analysis - use exec command for running models
    if [ -f "tools/lib/jdk-17/bin/java" ]; then
        export JAVA_HOME="$(pwd)/tools/lib/jdk-17"
        export PATH="$JAVA_HOME/bin:$PATH"
    fi
    $ALLOY_CMD exec docs/architecture/v0.0/alloy/client-factory.als > docs/architecture/v0.0/alloy/verification-results.txt 2>&1

    echo ""
    echo "✅ Alloy analysis completed!"
    echo "📄 Results saved to: docs/architecture/v0.0/alloy/verification-results.txt"
    echo ""
    echo "Key findings:"
    if [ -f "docs/architecture/v0.0/alloy/verification-results.txt" ]; then
        grep -E "(assert|check|found|no counterexample|counterexample)" docs/architecture/v0.0/alloy/verification-results.txt | head -10 || echo "Analysis complete - check full results"
    fi

tla-verify:
    #!/usr/bin/env sh
    echo "=== Running TLA+ temporal verification ==="

    # Get the justfile directory (project root)
    PROJECT_ROOT="$(dirname "$(readlink -f "${JUSTFILE:-justfile}")")"
    cd "$PROJECT_ROOT" || exit 1

    if [ -f "tools/bin/tlc" ]; then
        TLC_CMD="./tools/bin/tlc"
    elif command -v tlc >/dev/null 2>&1; then
        TLC_CMD="tlc"
    else
        echo "❌ TLA+ TLC not found. Please run: just setup-formal-tools"
        exit 1
    fi

    echo "🔍 Using TLA+ TLC: $TLC_CMD"
    echo "📁 Analyzing model: docs/architecture/v0.0/tla/client-factory.tla"
    echo ""

    # Create output directory
    mkdir -p docs/architecture/v0.0/tla/results

    # Run TLA+ model checking
    echo "Running temporal logic verification..."
    $TLC_CMD -workers auto -depth 100 -config docs/architecture/v0.0/tla/client-factory.cfg docs/architecture/v0.0/tla/client-factory.tla > docs/architecture/v0.0/tla/verification-results.txt 2>&1

    echo ""
    echo "✅ TLA+ analysis completed!"
    echo "📄 Results saved to: docs/architecture/v0.0/tla/verification-results.txt"
    echo ""
    echo "Key findings:"
    if [ -f "docs/architecture/v0.0/tla/verification-results.txt" ]; then
        grep -E "(Error|Exception|counterexample|Model checking completed)" docs/architecture/v0.0/tla/verification-results.txt | head -10 || echo "Analysis complete - check full results"
    fi

# Teja Pattern workflow commands
workflow-behavior:
    #!/usr/bin/env sh
    echo "=== Running complete behavior workflow ==="
    echo "This would normally run:"
    echo "1. Formal model analysis (if needed)"
    echo "2. Gherkin specification generation"
    echo "3. Schema generation"
    echo ""
    echo "For now, let's test the formal verification:"
    echo ""
    just alloy-verify

# Test commands
test-echo:
    #!/usr/bin/env sh
    echo "Justfile is working! 🎉"
    echo "This test command executes successfully."

test-java:
    #!/usr/bin/env sh
    echo "Testing Java installation..."
    if [ -f "tools/lib/jdk-17/bin/java" ]; then
        echo "✅ Java found: $(tools/lib/jdk-17/bin/java -version 2>&1 | head -1)"
    elif command -v java >/dev/null 2>&1; then
        echo "✅ Java found: $(java -version 2>&1 | head -1)"
    else
        echo "❌ Java not found"
        echo "Run: just setup-formal-tools"
    fi

# Setup command
setup:
    #!/usr/bin/env sh
    echo "=== Setting up development environment ==="
    just install
    echo ""
    echo "🔬 Setting up formal verification tools..."
    just setup-formal-tools-system
    echo ""
    echo "Environment setup completed"
    echo ""
    echo "Next steps:"
    echo "1. Run 'just alloy-verify' to test formal verification"
    echo "2. Run 'just workflow-behavior' to test Teja Pattern workflow"
    echo "3. Run 'just dev' to start development (when ready)"

# Help command
default:
    #!/usr/bin/env sh
    echo "Justfile commands for Teja Pattern Web App Template"
    echo ""
    echo "Setup:"
    echo "  just setup                    - Set up full development environment"
    echo "  just install                  - Install dependencies"
    echo "  just setup-formal-tools       - Check for Java/Alloy"
    echo "  just setup-formal-tools-global - Install Java/Alloy globally"
    echo "  just setup-formal-tools-local  - Install Java/Alloy locally"
    echo ""
    echo "Formal Verification:"
    echo "  just alloy-verify             - Run Alloy analysis on client factory model"
    echo ""
    echo "Workflow:"
    echo "  just workflow-behavior        - Run complete behavior workflow"
    echo ""
    echo "Development:"
    echo "  just dev                      - Start development servers"
    echo ""
    echo "Testing:"
    echo "  just test-echo                - Test Justfile functionality"
    echo "  just test-java                - Test Java installation"