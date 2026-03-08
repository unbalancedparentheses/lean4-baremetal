{
  description = "lean4-baremetal — Lean 4 on bare-metal RISC-V";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # RISC-V cross-compilation toolchain
        riscv-toolchain = pkgs.pkgsCross.riscv64.buildPackages.gcc;
        riscv-binutils = pkgs.pkgsCross.riscv64.buildPackages.binutils;

      in {
        devShells.default = pkgs.mkShell {
          name = "lean4-baremetal";

          buildInputs = with pkgs; [
            # Lean 4 compiler
            lean4

            # RISC-V 64-bit cross toolchain
            riscv-toolchain
            riscv-binutils

            # QEMU for running the bare-metal binary
            qemu

            # Useful tools
            gnumake
            file
          ];

          shellHook = ''
            echo "lean4-baremetal dev environment"
            echo "  lean:   $(lean --version 2>/dev/null || echo 'not found')"
            echo "  gcc:    $(riscv64-unknown-linux-gnu-gcc --version 2>/dev/null | head -1 || echo 'checking...')"
            echo "  qemu:   $(qemu-system-riscv64 --version | head -1)"
            echo ""
            echo "Commands:"
            echo "  make          - build the kernel"
            echo "  make lean-c   - compile Lean to C only"
            echo "  make run      - run on QEMU"
            echo "  make clean    - clean build artifacts"
          '';
        };
      });
}
