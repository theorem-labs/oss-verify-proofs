(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgMainSt.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f; symbols and
   section headers of the unstripped twin 635d02c7e8fa2e1653012207b6ddd2f2c5dd3b8e578ee9607cdc35b94e5260bb). What
   differs: the core imports are image B's lib/AU twins and lib/AU/PPgSat.v; the cuts are chosen on image B's code
   (its register allocation and block order differ from image A's); every cut keeps s9 = SB (slot 32) where image A
   keeps s6 = SB, because image B loads the shadow base into s9 (`ld s9,0(a1)` 0x80714); the flags byte is in s10
   (image A: s9) and the rest pointer / k in s5 / s6 (image A: s4 / s5); ss_C carries s11 = ~q, pinned to the new
   slot 106 (`not s11,s3` 0x80860), which the compiler's added pointer-overflow checks of the scan read
   (0x80894, 0x80a64); PM_RLO / PM_RHI are image B's .data.rel.ro start 0x97c20 and .got end 0x99e68
   (lib/AU/PPgLib.v RO_LO / RO_HI); INV_C adds the value of slot 106.

   The cut states of reac-pw/fuzz_pin's ASan harness walk at image B (LLVMFuzzerTestOneInput 0x806b4, 1092 bytes)
   and the invariant each carries: the interface every segment file lib/AU/PPgMain0 .. PPgMain5.v proves against.
   rule 24 (reuse): no function is proved here; this file states the five cut states and their invariants.

   The cuts (image B's addresses):
     ss_H 0x807d0  after the prologue, the class-1 frame and the size test (S0 -> S1);
     ss_Q 0x80848  after malloc returned a block, at `mv s3,a0` (S1 -> S2);
     ss_C 0x8088c  the ':' scan starts (`li s5,0`), the string is not empty (S2 -> S3);
     ss_D 0x808f0  want and want_label are computed, at `addi s11,s8,32` (S2 when the string is empty, S3 -> S4);
     ss_X 0x80968  after free returned (S4 -> S5, the exit).
   Every cut keeps the same frame part, as S0 leaves it: sp = sp1 (slot 70), s0 = sp0 (slot 2), s2 = s8 = F (slot
   75, the class-1 frame), s7 = SB + F / 8 (slot 88), s9 = SB (slot 32, the shadow base the instrumented checks add;
   dead in ss_X, where s9 holds the label cell's address), gp and tp; the frame's 16 shadow bytes (region 88,
   read-only, no chunk), the frame (region 75, the flag address at F + 120) and the 13 saved registers (region 2,
   [sp0 - 104, sp0)). The values a cut adds are pinned to the slots 100 (q, the block malloc returned), 101 (the rest
   pointer), 102 (k, the length of the spec string), 103 (the flags byte), 104 (want), 105 (want_label) and 106
   (~q = 2 ^ 64 - 1 - q); each invariant gives their values as functions of the input bytes c_pl
   (lib/Prog/pin_spec.v). Every other register is dead at the cut (fresh slots from PM_<cut>N). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgSat PPgMainRt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* ------------------------------ the registers at each cut ------------------------------ *)
(* ss_H 0x807d0: s3 = n (slot 11), s4 = p (slot 10), s9 = SB *)
Definition pm_H_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 26; 27; 28; 29; 30; 31]%nat.
Definition pm_H_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 26; 27; 28; 29; 30; 31]%bv.
Definition PM_HN : nat := 400.
Definition pm_H_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 11 0; SOff 10 0; SOff 21 0; SOff 22 0; SOff 88 0;
 SOff 75 0; SOff 32 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* ss_Q 0x80848: a0 = q (100), s5 = the rest pointer (101), s6 = k (102), s10 = the flags byte (103), s9 = SB *)
Definition pm_Q_deads : list nat := [1; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 27; 28; 29; 30; 31]%nat.
Definition pm_Q_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 27; 28; 29; 30; 31]%bv.
Definition PM_QN : nat := 500.
Definition pm_Q_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 100 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 19 0; SOff 20 0; SOff 101 0; SOff 102 0; SOff 88 0;
 SOff 75 0; SOff 32 0; SOff 103 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* ss_C 0x8088c: a0 = k (102, strlen's result), s3 = q (100), s10 = the flags byte (103), s11 = ~q (106), s9 = SB *)
Definition pm_C_deads : list nat := [1; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 28; 29; 30; 31]%nat.
Definition pm_C_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 28; 29; 30; 31]%bv.
Definition PM_CN : nat := 600.
Definition pm_C_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 102 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 100 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 88 0;
 SOff 75 0; SOff 32 0; SOff 103 0; SOff 106 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* ss_D 0x808f0: s3 = q (100), s4 = want (104), s5 = want_label (105), s10 = the flags byte (103), s9 = SB *)
Definition pm_D_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 22; 27; 28; 29; 30; 31]%nat.
Definition pm_D_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 22; 27; 28; 29; 30; 31]%bv.
Definition PM_DN : nat := 700.
Definition pm_D_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 100 0; SOff 104 0; SOff 105 0; SOff 22 0; SOff 88 0;
 SOff 75 0; SOff 32 0; SOff 103 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* ss_X 0x80968: the frame part only *)
Definition pm_X_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition pm_X_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition PM_XN : nat := 900.
Definition pm_X_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 88 0;
 SOff 75 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].

(* ------------------------------ the memory and the facts every cut keeps ------------------------------ *)
(* the save area as the prologue writes it (0x806bc-0x806ec, sp = sp0 - 128): s11 at sp0-104 .. ra at sp0-8 *)
Definition pm_saves : list YP09.chunk :=
[ YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition pm_mem : smem :=
[ YP09.mkRegion (Some 88%nat) 0 16 0 0 [];
  YP09.mkRegion (Some 75%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))];
  YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 pm_saves ].
(* S0's seven atoms: 88 = SB + F / 8, 87 = the flag address, 75 = F, 70 = sp1, 2 = sp0, 11 = n, 32 = SB *)
Definition pm_atoms : list (nat * afact) :=
[ (88%nat, mkAF (SB + 512) (SB + 2 ^ 44) 2); (87%nat, HPTR 0); (75%nat, HPTR 5); (70%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
  (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition pm_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)].

(* ------------------------------ the five cut states ------------------------------ *)
Definition ss_H : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x807d0 pm_H_regs pm_mem None (mkFacts pm_atoms [] pm_alias)) PM_HN pm_H_deads.
Definition ss_Q : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80848 pm_Q_regs pm_mem None
(mkFacts (pm_atoms ++ [(100%nat, HPTR 4); (101%nat, HPTR 0); (102%nat, mkAF 0 (2 ^ 26 - 1) 0); (103%nat, mkAF 0 255 0)]) [] pm_alias))
PM_QN pm_Q_deads.
Definition ss_C : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x8088c pm_C_regs pm_mem None
(mkFacts (pm_atoms ++ [(100%nat, HPTR 4); (102%nat, mkAF 1 (2 ^ 26 - 1) 0); (103%nat, mkAF 0 255 0)]) [] pm_alias))
PM_CN pm_C_deads.
Definition ss_D : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x808f0 pm_D_regs pm_mem None
(mkFacts (pm_atoms ++ [(100%nat, HPTR 4); (103%nat, mkAF 0 255 0)]) [] pm_alias))
PM_DN pm_D_deads.
Definition ss_X : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80968 pm_X_regs pm_mem None (mkFacts pm_atoms [] pm_alias)) PM_XN pm_X_deads.

(* ------------------------------ image B's table, the token / display pointers and the ':' set ------------------------------
   lib/AU/PPgSat.v's measured constants (fuzz_catalogue at 0x98000, the 11 token and 11 display pointers, the ':'
   set string at 0x20d80), under the walk's names. *)
Notation PM_CAT := PIN_CAT (only parsing).
Notation PM_TP := PIN_TP (only parsing).
Notation PM_DP := PIN_DP (only parsing).
Notation PM_COLONP := PIN_COLONP (only parsing).
(* the read-only window of the callee contracts' arodata_okP: image B's .data.rel.ro start .. .got end, the second
   disjunct of lib/AU/YCeh.v in_ro_tfa (lib/AU/PPgLib.v RO_LO / RO_HI) *)
Definition PM_RLO : Z := 0x97c20.
Definition PM_RHI : Z := 0x99e68.
(* ------------------------------ the harness's view, at image B's table ------------------------------ *)
(* the spec string: the input after the flags byte, cut at its first NUL (fuzz.h fuzz_str) *)
Definition pm_s (cx : rtcx) : list byte := pin_str (c_pl cx).
(* want (fuzz_pin.c:86-88) and want_label (:89-91), at image B's table PM_CAT and display pointers PM_DP;
   pin_spec.want_ptr / want_label state the same at the plain image's pointers *)
Definition pm_want (fl : Z) (s : list byte) : Z :=
match harness_want fl s with Some i => row_addr PM_CAT i | None => 0 end.
Definition pm_wlab (q fl : Z) (s : list byte) : Z :=
match harness_want fl s with
| Some i => match harness_label_off s with Some k => q + Z.of_nat k | None => PM_DP i end
| None => 0
end.

(* ------------------------------ the invariants ------------------------------ *)
Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
(* The harness's read-only fact (rt_base's arodata_ok over YCeh's in_ro_tfa) is the contracts' arodata_okP at
   image B's window [PM_RLO, PM_RHI): the read-only premise of every callee contract and of pin_ro_law. *)
Lemma pm_arodataP : forall (B : asyms) (rd : reader), arodata_ok B rd -> arodata_okP tfibsegs PM_RLO PM_RHI B rd.
Proof. intros B rd H a Ha. apply H. exact Ha. Qed.
(* ss_Q: one malloc so far; q, the rest pointer r, k and the flags byte pinned; the new block (q, k + 1) *)
Definition INV_Q (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q r kk fl,
ew E 100 = Z_to_bv 64 q /\ ew E 101 = Z_to_bv 64 r /\ ew E 102 = Z_to_bv 64 kk /\ ew E 103 = Z_to_bv 64 fl /\
kk = Z.of_nat (pin_k (c_pl cx)) /\ fl = pin_flags (c_pl cx) /\
r = (if c_n cx =? 0 then c_p cx else c_p cx + 1) /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk + 1)].
(* ss_C: the string s (k > 0 bytes, then its NUL) is in the block q; slot 106 holds ~q *)
Definition INV_C (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q kk fl,
ew E 100 = Z_to_bv 64 q /\ ew E 102 = Z_to_bv 64 kk /\ ew E 103 = Z_to_bv 64 fl /\ ew E 106 = Z_to_bv 64 (2 ^ 64 - 1 - q) /\
kk = Z.of_nat (pin_k (c_pl cx)) /\ 0 < kk /\ fl = pin_flags (c_pl cx) /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk + 1)] /\
garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) q (pin_zbytes (pm_s cx) ++ [0]).
(* ss_D: as ss_C (k may be 0; the block list up to order, since fuzz_catalogue_row's post keeps it up to a
   permutation), and want / want_label pinned at the harness's values *)
Definition INV_D (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q fl want wl,
ew E 100 = Z_to_bv 64 q /\ ew E 103 = Z_to_bv 64 fl /\ ew E 104 = Z_to_bv 64 want /\ ew E 105 = Z_to_bv 64 wl /\
fl = pin_flags (c_pl cx) /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(q, Z.of_nat (pin_k (c_pl cx)) + 1)]) /\
garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) q (pin_zbytes (pm_s cx) ++ [0]) /\
want = pm_want fl (pm_s cx) /\ wl = pm_wlab q fl (pm_s cx).
(* ss_X: the block is given back; the journal's two events (malloc and free) *)
Definition INV_X (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= RT_EV /\ acc <= c_T cx /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
End inv.
