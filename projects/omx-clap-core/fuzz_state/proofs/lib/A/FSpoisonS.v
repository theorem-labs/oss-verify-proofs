(* Ported from: a working branch 52efd1c871f7 proofs/omx-clap-core/fuzz_manifest/lib/A/FMpoisonS.v:1-46
   (a Theorem Labs lane, design/POISON.md section 7). Changed: module prefix fuzz_manifest -> fuzz_state, FMupoison -> FSupoison
   (lib/A/FSupoison.v, a Theorem Labs lane's ARU relocated), and the comment's file names and entry addresses (fs.asan's
   __asan_poison_memory_region / __asan_unpoison_memory_region, FSH_Base.PC_poison / PC_unpoison), and `getr` written
   YK11.getr, the definition it resolved to (lib/Lib/PropExec.v has its own getr / mkst / seg_rom, loaded wherever a
   lib/Prog module is; the qualified name keeps them out). No address in this file: the contracts are generic in the
   entry pc.
   ONE CONJUNCT STRONGER than a Theorem Labs lane's FMpoisonS.v: both contracts end with
   `(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)`, global presence monotonicity, in the position and
   spelling of YG0d.aintrin_realizes (lib/Reusable/YG0d.v:335) and A/FSupoisonU.aintrin_realizesU. Why: the donor's
   clauses give presence only on the stack window, and the aview equality outside the frame and the two shadow bytes
   does not give presence back (aview falls back to seg_rom where mem a = None), so the walk kit's fsw_intrin_atU
   (a working branch 259ea2daea9, through ajournal_after_write) could not consume them. Every other clause is
   the donor's text. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison.
Import ListNotations.
Local Open Scope Z_scope.
(* The contracts of __asan_poison_memory_region (h, 16) and __asan_unpoison_memory_region (h, 16) over ARU
   (A/FSupoison.v), for an 8-aligned head h in the whole user granules of a live block, the next granule in the same
   block. A/FSpoisonW.v proves them at fs.asan 0x54894 (FSH_Base.PC_poison) and 0x54a34 (FSH_Base.PC_unpoison).
   Design: a Theorem Labs lane's design/POISON.md section 7. *)
(* Both functions use a 64-byte frame; MemToShadow and musl memset use none. *)
Definition PO_WIN : Z := 64.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition apoison16_realizes (pc : Z) : Prop :=
forall ly S U (W : world segs) regs mem md h p n,
ecall_preU segs B ly S U W regs mem md ->
YK11.getr regs 10 = w64 h -> YK11.getr regs 11 = w64 16 ->
upoison_ok B ly S ((h, 16) :: U) ->
In (p, n) (ablocks B ly S) -> p <= h -> h + 16 < p + req_size n ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S ((h, 16) :: U) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PO_WIN <= a < spZ regs) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition aunpoison16_realizes (pc : Z) : Prop :=
forall ly S U (W : world segs) regs mem md h p n,
ecall_preU segs B ly S ((h, 16) :: U) W regs mem md ->
YK11.getr regs 10 = w64 h -> YK11.getr regs 11 = w64 16 ->
In (p, n) (ablocks B ly S) -> p <= h -> h + 16 < p + req_size n ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
aview segs (w_H W) mem' (shadow_addr h) = Some 0 /\ aview segs (w_H W) mem' (shadow_addr h + 1) = Some 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PO_WIN <= a < spZ regs) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End u.
