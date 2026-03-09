# Roadmap

This roadmap assumes the project is aiming to become the beginning of a reusable bare-metal Lean platform, not just a collection of one-off demos.

## Principles

- Keep the trusted computing base explicit and small.
- Favor reusable runtime and proof infrastructure over isolated examples.
- Prove one thing completely before scaling breadth.
- Add hardware support slowly; avoid board sprawl.
- Separate platform milestones from demo milestones.

## Phase 0: Stabilize the Current Base

Goal: make the existing repository reliable as a foundation.

Deliverables:
- End-to-end build, run, verify, and test flows work reliably under Nix.
- `Makefile` test targets stop reusing stale artifacts across examples.
- Runtime capabilities and limitations are documented clearly.
- The current SHA-256 example remains the canonical proof-bearing example.

Exit criteria:
- `make nix-test` is reliable on a clean checkout.
- `make nix-verify` is part of the normal validation story.
- The README and docs describe the current platform honestly.

## Phase 1: Complete the SHA-256 Proof Story

Goal: turn SHA-256 into the flagship end-to-end example for the platform.

Deliverables:
- Independent executable reference spec for SHA-256.
- Proof that implementation padding matches spec padding.
- Proof that message scheduling matches the SHA-256 reference recurrence.
- Proof that compression rounds match a reference round-step semantics.
- Final theorem connecting `sha256` to the independent reference spec for arbitrary inputs.

Exit criteria:
- The repo can defend a real end-to-end correctness claim for one nontrivial program.
- The proof file serves as the template for future verified platform components.

## Phase 2: Make the Runtime a Real Platform Surface

Goal: move from “custom runtime for one example” to “supported runtime subset for Lean on bare metal.”

Deliverables:
- Documented supported subset of Lean runtime features.
- Runtime tests for allocation, arrays, strings, refcounting, panic paths, and extern calls.
- Cleaner separation between runtime internals and example-specific code.
- Explicit policy for unsupported features such as bignums, threads, and OS-facing APIs.

Exit criteria:
- A new Lean example can be added without modifying the runtime in ad hoc ways.
- Runtime regressions are caught independently of example proofs.

## Phase 3: Add a Second Verified Systems Example

Goal: prove the approach generalizes beyond crypto.

Recommended target:
- Verified CAN or UART protocol parser.

Deliverables:
- A small parser or validator implemented in Lean and run on bare metal.
- Proofs of totality, decoding correctness, and bounds safety.
- Shared proof utilities extracted where appropriate.

Exit criteria:
- The repo contains at least two materially different verified bare-metal Lean programs.
- The second example reuses platform infrastructure rather than introducing one-off scaffolding.

## Phase 4: Real Hardware Bring-Up

Goal: prove the platform is not QEMU-only.

Deliverables:
- One supported physical RISC-V board.
- Board-specific boot, UART, and memory layout support.
- Reproducible instructions for flashing and running the verified examples on hardware.

Constraints:
- Support one board well before supporting multiple boards.
- Keep board support layered so QEMU remains the default development target.

Exit criteria:
- The flagship example runs on real hardware with the same proof story and build pipeline.

## Phase 5: Platform Libraries for Verified Bare-Metal Components

Goal: start building reusable libraries rather than isolated applications.

Candidate libraries:
- Packet / frame parsing utilities
- Bounded buffer and ring buffer structures
- Memory-region and capability checks
- Binary format and manifest parsing helpers
- Small hardware abstraction layers for UART, timers, and interrupts

Exit criteria:
- New examples are mostly composition of shared libraries plus small application logic.
- The platform starts to look like a reusable foundation for verified firmware components.

## Phase 6: Interrupts, Timers, and Controlled Concurrency

Goal: extend the platform into real embedded control flows without jumping directly to a microkernel.

Deliverables:
- Interrupt handling support
- Timer support
- Safe queue / mailbox patterns
- Verified invariants around simple event-driven execution

Exit criteria:
- The platform can express interrupt-driven firmware patterns without collapsing into unstructured C stubs.

## Phase 7: Secure Boot and Trusted Boot Components

Goal: add platform-level security components that justify the formal verification story.

Deliverables:
- Signed image loader or firmware manifest verifier
- Verified memory-region checks before handoff
- Clear trust boundary documentation for boot flow

Exit criteria:
- The project can credibly claim value for high-assurance embedded and security-sensitive systems.

## Phase 8: Toward a Minimal Lean Bare-Metal Kernel Substrate

Goal: explore whether the platform can support a tiny scheduler / kernel substrate.

Possible scope:
- Cooperative scheduler
- Fixed-priority arbiter
- Timer-driven task dispatch
- Simple verified queues and resource arbitration

Non-goal for this phase:
- Jumping directly to a full seL4-style kernel claim

Exit criteria:
- There is a minimal kernel-like substrate with explicit invariants and a believable proof surface.

## Ongoing Workstreams

These run across phases:

- Tooling: improve `lake`, `make`, and Nix ergonomics.
- Documentation: keep the proof claims precise and current.
- Proof engineering: extract reusable lemmas and avoid one-off proof tangles.
- Runtime discipline: keep unsupported Lean features explicit.
- Scope control: avoid drifting into “general embedded OS” too early.

## Near-Term Priority Order

1. Fix build/test reliability.
2. Finish the end-to-end SHA-256 proof.
3. Define and document the supported runtime surface.
4. Add a second verified systems example.
5. Port to one real RISC-V board.

## Success Criteria

The platform is succeeding if it can eventually support this workflow:

1. Write a small systems component in Lean.
2. Prove meaningful properties about that same code.
3. Compile it to freestanding C.
4. Link it against a documented bare-metal Lean runtime.
5. Run it on QEMU and one real board without changing the proof story.
