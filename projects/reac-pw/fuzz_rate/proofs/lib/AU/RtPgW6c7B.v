(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YFen.v, with its module paths and module names changed; 600 of its 644 lines of code are new or changed and 174 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c7.v at cb9cdc023f20; image B's code
   (fuzz_rate.asan-ubsan): its pcs, registers and real-frame cells, the pod e62 (F + 0x210) of the class-4 frame for
   locals instead of e (F + 0xf0) of the class-3 one, the multiplier cell R + 0x0, and the UBSan trap branches
   0x81890, 0x81ed4 (decided by the engine from the facts) and 0x81f24 (split, the trap arm refuted). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the block lemma w6cb_h7 of
   lib/AU/RtPgW6cBaseB.v, the head of case 7 of ent_build's `switch (kind % 10)` (pod.h:350-357) inside
   LLVMFuzzerTestOneInput, from the case entry 0x81888 to the entry of __asan_memcpy 0x518b8 (the `jal` at 0x81f3c).
   Proves no function (kind: segment lemma).

   THE CODE (RtPgW6cBaseB.v's header; s1 = R, s4 = SHADOW_OFF, s2 = c, s6 = |r|, s10 = c - 1, t1 = |r| + 1, a6 = 1):
     0x81888  beqz s6 -> 0x81b64        no byte: a1 := 0, a2 := 0, s6 := [R+0x150], -> 0x81f14
     0x8188c  addi a0,s2,1; bltu a6,a0  the trap test of s2 + 1 (taken: on to 0x81898; else `j 0x83098`)
     0x81898  the check of s2 (NE-SLOW, slow block 0x822bc), s6 := [R+0x150]; 0x818ac lbu a1 (= t); s2 := s10 + 2;
              a1 := t mod 21 (the multiply by 0x87, 0x818b4 .. 0x818e4); 0x818e8 e62.type := a1
     0x818ec  li a1,2; bne t1,a1 -> 0x81ed0   one byte left: a1 := 0, a2 := 0, -> 0x81f14
     0x81ed0  addi a1,s2,1; bltu a6,a1  the trap test; the check of s2 (NE-SLOW, 0x82320); 0x81eec lbu a2 (= s);
              a1 := t1 - 3; s2 := s10 + 3; a2 := s mod 12 (the multiply by [R+0x0] = 0x15555556)
     0x81f14  e62.size := a2; 0x81f18 bltu a2,a1 (a2 := min(a2, a1)); 0x81f20 not a0,s2; 0x81f24 bgeu a0,a2 (the
              trap test of s2 + a2); 0x81f2c s10 := s2 + a2, s8 := a1 - a2, a0 := [R+0x130], a1 := s2;
              0x81f3c jal __asan_memcpy.
   THE PROOF. One engine state per arm (r = [], [t], t :: s :: r2), over the environment Ereg regs (w7b_extra F t s)
   (atom 32 = F + 0x210 the address of e62, 33 = t, 34 = s), token-engine runs (lib/Reusable/YCbn.v, YCbq.v
   aj_run_to_tok) to 0x518b8. The trap tests of s2 + 1 the engine decides itself: a6 has the atom fact [1, 1] and the
   cursor s2 is pinned to s10 + 1 with s10's atom in the numeral range [0, 2^47 - 3], so s2 + 1 >= 2 > 1. The trap
   test `not a0,s2; bgeu a0,a2` it cannot decide (no range of a complement): every arm stops there, is split by
   srr_branch_tok (YCbm.v), and its trap half is refuted from c + |r| <= 2^63 (YI08.U_not_off). The arm with two
   bytes also stops at the data-dependent `bltu` 0x81f18 and is split there first. The regions: e62's header
   [F + 0x210, F + 0x218) based at atom 32 with the write window [0, 8) and two zero words; the cells [R, R+8),
   [R+0x130, R+0x138) and [R+0x150, R+0x158) based at s1 (the input avoids them, w6cb_in); the input bytes read (one
   or two) based at s10. s6 is pinned to 0 on the no-byte arm, t1 to 2 on the one-byte arm, and atom facts on s6 and
   t1 decide the other branches. e62's window is outside the shadow band (it lies in the frame (4, pos) of the
   application's memory): the engine's static check takes it from the shadow entry mkSHE 32 8 0
   (lib/Reusable/YCbq.v shent_app_of_frame). The values t mod 21 and s mod 12 the engine leaves as expressions in one
   atom each are checked for all 256 byte values (w7_mod_val). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW6cBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the engine states ======================================== *)
Definition w7b_extra (F t s : Z) : list word := [w64 (F + 0x210); w64 t; w64 s].
Definition w7b_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0x15555556))].
Definition w7b_rB : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0 [YP09.mkChunk 0x130 (CVal 8 (SOff 32 8))].
Definition w7b_rC : YP09.region := YP09.mkRegion (Some 9%nat) 0x150 0x158 0 0 [YP09.mkChunk 0x150 (CVal 8 (SOff 32 0))].
Definition w7b_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8
  [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SLit 0))].
Definition w7b_rI (m : nat) : YP09.region := YP09.mkRegion (Some 26%nat) 1 (1 + Z.of_nat m) 0 0
  (firstn m [YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))]).
Definition w7b_mem (m : nat) : smem :=
  w7b_rE :: w7b_rA :: w7b_rB :: w7b_rC :: match m with O => [] | S _ => [w7b_rI m] end.
(* the shadow base of the checks is s4's own atom, pinned to SHADOW_OFF by a fact *)
Definition w7b_Bx : sv := SOff 20 0.
Definition w7b_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* e62's write window [0, 8) of atom 32, an application window apart from the shadow band *)
Definition w7b_SH : list shent := [mkSHE 32 8 0].
Definition w7b_sh20 : nat * afact := (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
(* every atom bound is a closed numeral *)
Definition w7b_f0 : facts := mkFacts [w7b_sh20] [] [].
Definition w7b_f1 : facts := mkFacts [w7b_sh20; (26%nat, mkAF 0 (2 ^ 47 - 3) 0); (22%nat, mkAF 1 1 0);
  (16%nat, mkAF 1 1 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)] [] [].
Definition w7b_f2 : facts := mkFacts [w7b_sh20; (26%nat, mkAF 0 (2 ^ 47 - 3) 0); (22%nat, mkAF 2 (2 ^ 47) 0);
  (6%nat, mkAF 3 (2 ^ 47 + 1) 0); (16%nat, mkAF 1 1 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)] [] [].
Definition w7b_sr0 : list sv := sr_set (sr_set sr_atoms (18%bv : bv 5) (SOff 26 1)) (22%bv : bv 5) (SLit 0).
Definition w7b_sr1 : list sv := sr_set (sr_set sr_atoms (18%bv : bv 5) (SOff 26 1)) (6%bv : bv 5) (SLit 2).
Definition w7b_sr2 : list sv := sr_set sr_atoms (18%bv : bv 5) (SOff 26 1).

(* ======================================== the arithmetic ======================================== *)
(* an sv whose only atom is n *)
Fixpoint w7_on (n : nat) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff m _ => Nat.eqb m n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => w7_on n a && w7_on n b
| SExt _ _ a => w7_on n a
| SData _ _ _ => false
| SF1 _ a => w7_on n a
| SF2 _ a b => w7_on n a && w7_on n b
| SF3 _ a b c => w7_on n a && w7_on n b && w7_on n c
end.
Section ar. Context {fx : YK11.FPState}.
Lemma w7_on_denot : forall n E E' v, ew E' n = ew E n -> w7_on n v = true -> sv_denot E' v = sv_denot E v.
Proof.
intros n E E' v HA. induction v; cbn; intros H; try reflexivity; try discriminate H;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
- apply Nat.eqb_eq in H. subst n0. rewrite HA. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv by assumption. reflexivity.
- rewrite IHv by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2, IHv3 by assumption. reflexivity.
Qed.
(* every atom holds z *)
Definition w7_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
(* e denotes v mod m in w7_envz v, for each v in [0, 256) *)
Definition w7_chk (e : sv) (m : Z) : bool :=
forallb (fun k => bv_eqb (sv_denot (w7_envz (Z.of_nat k)) e) (Z_to_bv 64 (Z.of_nat k mod m))) (seq 0 256).
Lemma w7_mod_val : forall n E v m e, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> w7_on n e = true -> w7_chk e m = true ->
sv_denot E e = Z_to_bv 64 (v mod m).
Proof.
intros n E v m e Hn Hv Ho Hc.
rewrite (w7_on_denot n (w7_envz v) E e) by first [rewrite Hn; reflexivity | exact Ho].
unfold w7_chk in Hc. rewrite forallb_forall in Hc. specialize (Hc (Z.to_nat v) ltac:(apply in_seq; lia)).
cbv beta in Hc. rewrite Z2Nat.id in Hc by lia. apply bv_eqb_true_iff. exact Hc.
Qed.
Lemma w7_mod_U : forall n E v m e, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> 0 < m <= 256 ->
w7_on n e = true -> w7_chk e m = true -> U E e = v mod m.
Proof.
intros n E v m e Hn Hv Hm Ho Hc. unfold U. rewrite (w7_mod_val n E v m e Hn Hv Ho Hc).
apply unsigned_lit_small. pose proof (Z.mod_pos_bound v m ltac:(lia)). lia.
Qed.
Lemma w7_U_w64 : forall E e z, 0 <= z < 2 ^ 64 -> U E e = z -> sv_denot E e = w64 z.
Proof. intros E e z Hz H. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia. exact H. Qed.
Lemma w7_af0 : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi H Hv Hb. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
End ar.

(* a register other than x0 *)
Ltac w7_ne0 := let X := fresh "X" in intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X.

(* the windows of a list of regions: only atom 32's, inside [0, 8) *)
Definition w7_win_ok (rs : smem) : bool :=
forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
  match YP09.r_base r with Some n => Nat.eqb n 32 && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 8) | None => false end) rs.

Ltac w7_zc := repeat match goal with |- context [zcanon ?z] =>
  lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_id z) by (unfold M64; lia) end end.
Ltac w7_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; w7_kio].
(* the side goals of w7_mod_val / w7_mod_U: the atom (A at the entry's environment, A' at the run's), the bounds,
   and the two closed checks *)
Ltac w7_side A A' := first [exact A' | (rewrite ?ew_ewset_other by lia; exact A) | lia | (vm_compute; reflexivity)].
(* a chunk's value bound 0 <= v < 2 ^ 32 (from the hypotheses, or closed) and the chunk size *)
Ltac w7_cl := vm_compute; first [reflexivity | (intros X; discriminate X) | (split; [intros X; discriminate X | reflexivity])].
Ltac w7_bnd := first [ (change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia) | w7_cl ].
(* an atom fact of the run's environment, from the entry's *)
Ltac w7_at A := rewrite ?ew_ewset_other by lia; exact A.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w7_wr_in : forall E rs a, w7_win_ok rs = true -> in_wrange E rs a ->
bv_unsigned (ew E 32) <= a < bv_unsigned (ew E 32) + 8.
Proof.
intros E rs a Hok (r & Hin & Ha). unfold w7_win_ok in Hok. rewrite forallb_forall in Hok.
specialize (Hok r Hin). apply orb_prop in Hok as [Hro | Hb].
- apply Z.leb_le in Hro. lia.
- destruct (YP09.r_base r) as [n|] eqn:Hbase; [|discriminate Hb].
  apply andb_prop in Hb as [Hb Hhi]. apply andb_prop in Hb as [Hn Hlo].
  apply Nat.eqb_eq in Hn. subst n. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  try rewrite Hbase in Ha. cbn [base_val] in Ha. lia.
Qed.
(* e62's header lies in the class-4 frame (4, pos) *)
Lemma w7b_awr : forall E rs STK sp0 FP bl0 blc ly own pos F,
w7_win_ok rs = true -> In (4, pos) own -> F = frame_addr ly 4 pos -> bv_unsigned (ew E 32) = F + 0x210 ->
awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own pos F Hok Hown HF U32 a Ha.
pose proof (w7_wr_in E rs a Hok Ha) as Hw. rewrite U32 in Hw.
apply (rtsb_awr_fobj STK sp0 FP bl0 blc ly own pos a Hown). rewrite <- HF. lia.
Qed.
(* a run's frame keeps every byte outside e62's header *)
Lemma w7b_keep : forall E rs H (m0 m1 m2 : word -> option byte) F,
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> w7_win_ok rs = true -> bv_unsigned (ew E 32) = F + 0x210 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 F HFr Hok U32 K a Ha Hn. rewrite <- (K a Ha Hn).
apply (aview_eq_of rsegs). apply HFr. rewrite unsigned_lit_small by lia.
intros Hw. apply Hn. pose proof (w7_wr_in E rs a Hok Hw) as Hw'. rewrite U32 in Hw'. unfold w6cb_hdr_wr. lia.
Qed.
(* a chunk of region i of a final state, at absolute address a *)
Lemma w7_val_at : forall E ss H ms i r off (n : N) e v b a,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> a = b + off ->
val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v b a HS Hi Hc Hb He Hv Hn ->.
pose proof (rtsb_region_nth E ss ms i r H HS Hi) as Hok.
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (val_of_chunk_ok rsegs E _ b off n e v Hck He Hv Hn).
Qed.

(* ---- the entry state of every arm (m input bytes read) ---- *)
Lemma w7b_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) (R F c t s : Z) (m : nat) (sr : list sv) (G : facts),
regs_ok (Ereg regs (w7b_extra F t s)) sr regs ->
facts_ok (Ereg regs (w7b_extra F t s)) G ->
(m <= 2)%nat ->
getr regs 9 = w64 R -> getr regs 26 = w64 (c - 1) ->
0 <= R -> R + 0x158 <= 2 ^ 64 -> 4096 <= F -> F + 0x218 <= R ->
1 <= c -> c + 2 <= 2 ^ 64 ->
0 <= t < 256 -> 0 <= s < 256 ->
(forall o, 0 <= o < 8 -> apresent (w_H W) memc (F + 0x210 + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x218) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x0) 8 0x15555556 ->
val_mem rsegs (mrestrict (w_H W) memc) (F + 0x210 + 0) 4 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (F + 0x210 + 4) 4 0 ->
((1 <= m)%nat -> val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 1) 1 t) ->
((2 <= m)%nat -> val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 2) 1 s) ->
(forall a, c <= a < c + Z.of_nat m -> ~ (R + 0x0 <= a < R + 0x8) /\ ~ (R + 0x130 <= a < R + 0x138) /\
  ~ (R + 0x150 <= a < R + 0x158) /\ ~ (F + 0x210 <= a < F + 0x218)) ->
st_ok rsegs (Ereg regs (w7b_extra F t s)) (mkSS W6CB_D7 sr (w7b_mem m) None G)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D7) memc (seg_rom rsegs))).
Proof.
intros W memc regs R F c t s m sr G Hsr HG Hm H9 H26 HR0 HR1 HF0 HFR Hc0 Hc1 Ht Hs Hp
  V150 V130 V0 Vt0 Vs0 Vt Vs Hd.
assert (U9 : bv_unsigned (ew (Ereg regs (w7b_extra F t s)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (Ereg regs (w7b_extra F t s)) 26) = c - 1)
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), H26; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (w7b_extra F t s)) 32 = w64 (F + 0x210)) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew (Ereg regs (w7b_extra F t s)) 33 = w64 t) by exact (ew_Ereg_extra regs _ 1).
assert (E34 : ew (Ereg regs (w7b_extra F t s)) 34 = w64 s) by exact (ew_Ereg_extra regs _ 2).
assert (U32 : bv_unsigned (ew (Ereg regs (w7b_extra F t s)) 32) = F + 0x210)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); [exact Hsr | | | | exact HG].
- destruct m as [|[|[|m]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia].
- unfold w7b_mem. constructor; [|constructor; [|constructor]].
  + unfold w7b_rE. apply (rtmb_rw_region rsegs _ (w_H W) memc 32 (F + 0x210)); [exact U32 | lia | lia | |].
    * intros o Ho. apply Hp. lia.
    * constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val rsegs _ _ (F + 0x210) 0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact Vt0].
      -- apply (chunk_ok_val rsegs _ _ (F + 0x210) 4 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact Vs0].
  + unfold w7b_rA. apply (rtmb_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0 8 (SLit 0x15555556) 0x15555556); [reflexivity | cbn; lia | cbn; lia | exact V0].
  + unfold w7b_rB. apply (rtmb_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 32 8) (F + 0x218)); [| cbn; lia | cbn; lia | exact V130].
    cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  + destruct m as [|m'].
    * unfold w7b_rC. constructor; [|constructor].
      apply (rtmb_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 32 0) (F + 0x210)); [| cbn; lia | cbn; lia | exact V150].
      cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * constructor; [|constructor; [|constructor]].
      -- unfold w7b_rC. apply (rtmb_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |]. constructor; [|constructor].
         apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 32 0) (F + 0x210)); [| cbn; lia | cbn; lia | exact V150].
         cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
      -- unfold w7b_rI. apply (rtmb_ro_region rsegs _ (w_H W) memc 26 (c - 1)); [exact U26 | lia | lia |].
         assert (C1 : YP09.chunk_ok rsegs (Ereg regs (w7b_extra F t s)) (mrestrict (w_H W) memc) (c - 1)
           (YP09.mkChunk 1 (CVal 1 (SOff 33 0)))).
         { apply (chunk_ok_val rsegs _ _ (c - 1) 1 1 (SOff 33 0) t); [| cbn; lia | cbn; lia | exact (Vt ltac:(lia))].
           cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
         destruct m' as [|[|m'']]; cbn [firstn].
         ++ constructor; [exact C1 | constructor].
         ++ constructor; [exact C1 | constructor; [|constructor]].
            apply (chunk_ok_val rsegs _ _ (c - 1) 2 1 (SOff 34 0) s); [| cbn; lia | cbn; lia | exact (Vs ltac:(lia))].
            cbn [sv_denot]. rewrite E34. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
         ++ lia.
- unfold w7b_mem, w7b_rE, w7b_rA, w7b_rB, w7b_rC, w7b_rI.
  destruct m as [|[|[|m]]]; [| | | lia];
  cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U26, ?U32.
  + repeat split; lia.
  + pose proof (Hd c ltac:(cbn; lia)) as D0. repeat split; lia.
  + pose proof (Hd c ltac:(cbn; lia)) as D0. pose proof (Hd (c + 1) ltac:(cbn; lia)) as D1. repeat split; lia.
Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* the shadow entry of e62's window *)
Lemma w7b_shok : forall E lyc Sc (W : world rsegs) memc mdc F pos M,
AR rsegs B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
U E w7b_Bx = SHADOW_OFF -> U E (SOff 32 0) = F + 0x210 -> sh_ok rsegs w7b_Bx w7b_SH E M.
Proof.
intros E lyc Sc W memc mdc F pos M HAR Hin HF HB H32. constructor; [|constructor].
apply (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc E w7b_Bx 32 (F + 0x210) 4 pos 0 8 M HAR Hin);
  [exact HB | exact H32 | rewrite <- HF; lia | lia | rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia].
Qed.

(* the statement for one shape of r (w6cb_h7_stmt's body, word for word) *)
Definition w7b_goal (r : list byte) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z),
w6cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6cb_regs B regs R c (Z.of_nat (length r)) -> w6cb_cells W memc R F -> w6cb_in W memc R F c r ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (zeros 104) ->
SRr rsegs W (cfg_at rsegs W6CB_D7 regs memc mdc)
(w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_CPY w6cb_clob67 (w6cb_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let s := fst (fuzz_u8 r1) in let r2 := snd (fuzz_u8 r1) in
 let n := Z.min (s mod 12) (Z.of_nat (length r2)) in
 let src := c + Z.of_nat (length r) - Z.of_nat (length r2) in
 getr regs2 1 = w64 W6CB_RCPY /\ getr regs2 10 = w64 (F + 0x218) /\ getr regs2 11 = w64 src /\
 getr regs2 12 = w64 n /\ getr regs2 22 = w64 (F + 0x210) /\ getr regs2 24 = w64 (Z.of_nat (length r2) - n) /\
 getr regs2 26 = w64 (src + n) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 (t mod 21) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 (s mod 12))).

(* the premises taken apart, and the frame's geometry *)
Ltac w7b_pre Hctx Hregs Hcells Hin :=
  destruct Hctx as (HJ & (HR16 & HSTK & HRsp & HRk & Hown & HF & HFapp & HF32) & Hrom);
  destruct Hregs as (H2 & H3 & H4 & H9 & H20 & H18 & H22 & H26 & H6 & H16);
  destruct Hcells as (V150 & V130 & V0);
  destruct Hin as (Hbytes & Hra & Hhull & Hc1 & Hc63 & Hamr & Hdis);
  pose proof rtsb_wx as Hwx; pose proof rtsb_segs_low as Hsl;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc ?W ?memc ?mdc _, Hown : In (4, ?pos) _,
    HF : ?F = frame_addr _ 4 _ |- _ =>
    pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _);
    pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _);
    assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown);
    destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & HFpres & _);
    destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _);
    rewrite <- HF in HFpres, HF4096, HFceil; change (fs_frame_bytes 4) with 1024 in HFpres, HFceil
  end;
  unfold T_SEG_STK, ASTACK in HSTK, HRk, Hdis;
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr, HRk.

(* the registers of a final state, as their symbolic values *)
Ltac w7_reg HS r :=
  lazymatch type of HS with st_ok _ ?Ex ?ssf (restrict _ ?msx) =>
    rewrite (st_ok_restrict_reg rsegs _ Ex ssf msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssf) r) in
    replace (sr_get (ss_regs ssf) r) with e by (vm_compute; reflexivity)
  end.
(* a U goal: unfold the engine's sums, the one-atom remainders by w7_mod_U, then the atoms *)
Ltac w7_Ueval tac :=
  repeat first [ progress tac | rewrite U_SAlu | rewrite U_SOff | rewrite U_SLit ];
  cbn [zalu_raw]; rewrite ?ew_ewset_other by lia.

(* the leaf at the memcpy's entry: everything but Q *)
Ltac w7_leaf HS HJ KE kept :=
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    apply SRr_ret; red; exists (ms_regs msx), (ms_mem msx), mdx;
    split; [reflexivity|];
    split; [rewrite (st_ok_restrict_mkst rsegs _ _ _ msx HS eq_refl) at 1; reflexivity|];
    split; [exact HJ|];
    split; [w7_kio|];
    split; [kept|];
    split; [exact KE|];
    cbv beta zeta
  end end.

(* the bytes the run keeps outside e62's header, from the bytes the runs before it kept *)
Ltac w7b_ke KE W memc F U32 Kprev :=
  lazymatch goal with HFr : frame_of _ _ _ (mrestrict _ (ms_mem ?msx)) |- _ =>
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a ->
      aview rsegs (w_H W) (ms_mem msx) a = aview rsegs (w_H W) memc a)
    by (eapply (w7b_keep _ _ _ memc _ _ F HFr); [vm_compute; reflexivity | w7_at U32 | Kprev]);
    clear HFr
  end.

(* the environment of the U terms of a hypothesis *)
Ltac w7b_envof H := lazymatch type of H with context [U ?Ex _] => Ex end.
(* rewrite U Ex (SOff n k) in H from the atom fact A : ew (entry) n = w64 x *)
Ltac w7b_Uoff H A :=
  lazymatch type of A with ew _ ?n = w64 ?x =>
  lazymatch type of H with context [U ?Ex (SOff n ?k)] =>
    let A' := fresh "A'" in
    assert (A' : ew Ex n = Z_to_bv 64 x) by w7_at A;
    rewrite (U_atom_off Ex n x k A') in H by lia; clear A'
  end end.

(* the trap arm of `not a0,s2; bgeu a0,a2` at 0x81f24 (fall-through to `j 0x83098`): there a0 = ~s2 <u a2; turn
   that into a Z fact over s2 = s10 + k *)
Ltac w7b_trap Hc A26 :=
  exfalso; rewrite branch_geu_U in Hc; apply Bool.negb_false_iff, Z.ltb_lt in Hc;
  lazymatch type of A26 with ew _ 26 = w64 ?x =>
  lazymatch type of Hc with context [U ?Ex (SAlu ALU_XOR (SOff 26 ?k) (SLit _))] =>
    let A' := fresh "A'" in
    assert (A' : ew Ex 26 = Z_to_bv 64 x) by w7_at A26;
    rewrite (YI08.U_not_off Ex 26 x k A') in Hc by lia; clear A'
  end end.

(* the check obligations of a run: s2 = s10 + 1 or s10 + 2 inside the input [c, c + len) *)
Ltac w7b_obl Hra A20 A26 :=
  eapply (obl_of_range rsegs _ _ _ _ _ _ _ _ Hra);
  [ unfold w7b_Bx; apply (U_atom _ 20 SHADOW_OFF A20); unfold SHADOW_OFF; lia
  | first [rewrite (U_atom_off _ 26 _ 1 A26) by lia | rewrite (U_atom_off _ 26 _ 2 A26) by lia]; lia
  | first [rewrite (U_atom_off _ 26 _ 1 A26) by lia | rewrite (U_atom_off _ 26 _ 2 A26) by lia]; lia ].

(* ======================================== no byte left ======================================== *)
Lemma w7b_arm0 : w7b_goal [].
Proof using LAWS.
unfold w7b_goal. intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c Hctx Hregs Hcells Hin Hz.
w7b_pre Hctx Hregs Hcells Hin. cbn [length] in *.
assert (A9 : ew (Ereg regs (w7b_extra F 0 0)) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (A26 : ew (Ereg regs (w7b_extra F 0 0)) 26 = w64 (c - 1))
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (A20 : ew (Ereg regs (w7b_extra F 0 0)) 20 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (A32 : ew (Ereg regs (w7b_extra F 0 0)) 32 = w64 (F + 0x210)) by exact (ew_Ereg_extra regs _ 0).
assert (U32 : bv_unsigned (ew (Ereg regs (w7b_extra F 0 0)) 32) = F + 0x210)
  by (rewrite A32; unfold w64; apply unsigned_lit_small; lia).
assert (HSR : regs_ok (Ereg regs (w7b_extra F 0 0)) w7b_sr0 regs).
{ unfold w7b_sr0. apply regs_ok_pin; [apply regs_ok_pin | |].
  - apply regs_ok_Ereg.
  - w7_ne0.
  - rewrite H18. cbn [sv_denot]. rewrite A26. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  - w7_ne0.
  - rewrite H22. reflexivity. }
assert (HFG : facts_ok (Ereg regs (w7b_extra F 0 0)) w7b_f0).
{ unfold facts_ok, w7b_f0, w7b_sh20. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I].
  apply (w7_af0 _ _ _ _ _ A20); unfold SHADOW_OFF; lia. }
pose proof (w7b_entry W memc regs R F c 0 0 0%nat w7b_sr0 w7b_f0 HSR HFG ltac:(lia) H9 H26
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; apply (proj1 (HFpres (F + 0x210 + o) ltac:(lia)))) V150 V130 V0
  ltac:(apply (rtmb_bytes_field rsegs _ _ _ _ 0%nat 4%nat 0 Hz); [reflexivity | cbn; lia])
  ltac:(apply (rtmb_bytes_field rsegs _ _ _ _ 4%nat 4%nat 0 Hz); [reflexivity | cbn; lia])
  ltac:(intros X; lia) ltac:(intros X; lia) ltac:(intros a Ha; cbn in Ha; lia)) as HS.
assert (SHOK : sh_ok rsegs w7b_Bx w7b_SH (Ereg regs (w7b_extra F 0 0)) (mrestrict (w_H W) memc)).
{ apply (w7b_shok _ lyc Sc W memc mdc F pos _ HAR Hin4 HF).
  - unfold w7b_Bx. apply (U_atom _ 20 SHADOW_OFF A20). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 (F + 0x210) A32). lia. }
assert (HAE : env_agree 32 (Ereg regs (w7b_extra F 0 0)) (Ereg regs (w7b_extra F 0 0))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6CB_D7) with (Z_to_bv 64 W6CB_D7).
(* 0x81888 .. the trap test 0x81f24 *)
aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
{ eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | exact U32]. }
w7b_ke KE1 W memc F U32 ltac:(intros; reflexivity).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (HAE' : env_agree 32 (Ereg regs (w7b_extra F 0 0)) Ex) by env_agree_chain HAE end.
srr_branch_tok w6cb_tbl_ok HS SHOK w7b_Bspan.
- aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
  { eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | w7_at U32]. }
  w7b_ke KE W memc F U32 ltac:(exact KE1).
  w7_leaf HS HJ KE ltac:(eapply (regs_kept_of_st_ok rsegs _ _ _ regs (w7b_extra F 0 0) (w_H W) _ HS);
    [env_agree_chain HAE' | vm_compute; reflexivity]).
  cbn [Cursor.fuzz_u8 fst snd length].
  split; [w7_reg HS (1%bv : bv 5); reflexivity|].
  split; [w7_reg HS (10%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [w7_reg HS (11%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A26; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [w7_reg HS (12%bv : bv 5); reflexivity|].
  split; [w7_reg HS (22%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [w7_reg HS (24%bv : bv 5); reflexivity|].
  split; [w7_reg HS (26%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A26; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split.
  + eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 0 4%N _ _ (F + 0x210) _ HS); [reflexivity | cbn [YP09.r_chunks In];
      repeat (first [left; reflexivity | right]) | w7_at U32 | reflexivity | w7_bnd | w7_bnd | lia].
  + eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 4 4%N _ _ (F + 0x210) _ HS); [reflexivity | cbn [YP09.r_chunks In];
      repeat (first [left; reflexivity | right]) | w7_at U32 | reflexivity | w7_bnd | w7_bnd | lia].
- (* the trap arm: ~c <u 0 is false *)
  w7b_trap Hc A26. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc. lia.
Qed.

(* ======================================== one byte left ======================================== *)
Lemma w7b_arm1 : forall t0, w7b_goal [t0].
Proof using LAWS.
intros t0. unfold w7b_goal.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c Hctx Hregs Hcells Hin Hz.
w7b_pre Hctx Hregs Hcells Hin. cbn [length] in *.
pose proof (Cursor.byte_range t0) as Ht. set (t := bv_unsigned t0) in *.
assert (A9 : ew (Ereg regs (w7b_extra F t 0)) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (A26 : ew (Ereg regs (w7b_extra F t 0)) 26 = w64 (c - 1))
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (A20 : ew (Ereg regs (w7b_extra F t 0)) 20 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (A22 : ew (Ereg regs (w7b_extra F t 0)) 22 = w64 (Z.of_nat 1))
  by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (A16 : ew (Ereg regs (w7b_extra F t 0)) 16 = w64 1)
  by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
assert (A32 : ew (Ereg regs (w7b_extra F t 0)) 32 = w64 (F + 0x210)) by exact (ew_Ereg_extra regs _ 0).
assert (A33 : ew (Ereg regs (w7b_extra F t 0)) 33 = w64 t) by exact (ew_Ereg_extra regs _ 1).
assert (A34 : ew (Ereg regs (w7b_extra F t 0)) 34 = w64 0) by exact (ew_Ereg_extra regs _ 2).
assert (U32 : bv_unsigned (ew (Ereg regs (w7b_extra F t 0)) 32) = F + 0x210)
  by (rewrite A32; unfold w64; apply unsigned_lit_small; lia).
assert (D0 := Hdis c ltac:(lia)).
assert (HSR : regs_ok (Ereg regs (w7b_extra F t 0)) w7b_sr1 regs).
{ unfold w7b_sr1. apply regs_ok_pin; [apply regs_ok_pin | |].
  - apply regs_ok_Ereg.
  - w7_ne0.
  - rewrite H18. cbn [sv_denot]. rewrite A26. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  - w7_ne0.
  - rewrite H6. reflexivity. }
assert (HFG : facts_ok (Ereg regs (w7b_extra F t 0)) w7b_f1).
{ unfold facts_ok, w7b_f1, w7b_sh20. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I].
  split; [apply (w7_af0 _ _ _ _ _ A20); unfold SHADOW_OFF; lia|].
  split; [apply (w7_af0 _ _ _ _ _ A26); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A22); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A16); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A33); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A34); lia|].
  exact I. }
pose proof (w7b_entry W memc regs R F c t 0 1%nat w7b_sr1 w7b_f1 HSR HFG ltac:(lia) H9 H26
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; apply (proj1 (HFpres (F + 0x210 + o) ltac:(lia)))) V150 V130 V0
  ltac:(apply (rtmb_bytes_field rsegs _ _ _ _ 0%nat 4%nat 0 Hz); [reflexivity | cbn; lia])
  ltac:(apply (rtmb_bytes_field rsegs _ _ _ _ 4%nat 4%nat 0 Hz); [reflexivity | cbn; lia])
  ltac:(intros _; replace (c - 1 + 1) with (c + Z.of_nat 0) by lia;
        exact (rtmb_bytes_byte rsegs _ _ _ _ 0%nat Hbytes ltac:(cbn; lia)))
  ltac:(intros X; lia)
  ltac:(intros a Ha; assert (a = c) by (cbn in Ha; lia); subst a; lia)) as HS.
assert (SHOK : sh_ok rsegs w7b_Bx w7b_SH (Ereg regs (w7b_extra F t 0)) (mrestrict (w_H W) memc)).
{ apply (w7b_shok _ lyc Sc W memc mdc F pos _ HAR Hin4 HF).
  - unfold w7b_Bx. apply (U_atom _ 20 SHADOW_OFF A20). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 (F + 0x210) A32). lia. }
assert (HAE : env_agree 32 (Ereg regs (w7b_extra F t 0)) (Ereg regs (w7b_extra F t 0))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6CB_D7) with (Z_to_bv 64 W6CB_D7).
(* 0x81888 .. the trap test 0x81f24: the trap test of s2 + 1, the check of s2, e62.type and e62.size stored *)
aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
{ w7b_obl Hra A20 A26. }
{ eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | exact U32]. }
w7b_ke KE1 W memc F U32 ltac:(intros; reflexivity).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (HAE' : env_agree 32 (Ereg regs (w7b_extra F t 0)) Ex) by env_agree_chain HAE end.
srr_branch_tok w6cb_tbl_ok HS SHOK w7b_Bspan.
- aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
  { eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | w7_at U32]. }
  w7b_ke KE W memc F U32 ltac:(exact KE1).
  w7_leaf HS HJ KE ltac:(eapply (regs_kept_of_st_ok_pins rsegs _ _ _ regs (w7b_extra F t 0) (w_H W) _
    [(6%bv, SLit 2)] HS);
    [env_agree_chain HAE'
    | intros r0 e0 [He|[]]; injection He as <- <-; cbn [sv_denot]; rewrite H6; reflexivity
    | vm_compute; reflexivity]).
  cbn [Cursor.fuzz_u8 fst snd length]. fold t.
  split; [w7_reg HS (1%bv : bv 5); reflexivity|].
  split; [w7_reg HS (10%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [w7_reg HS (11%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A26; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [w7_reg HS (12%bv : bv 5); reflexivity|].
  split; [w7_reg HS (22%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [w7_reg HS (24%bv : bv 5); reflexivity|].
  split; [w7_reg HS (26%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A26; unfold w64;
    rewrite unsigned_lit_small by lia; f_equal; lia|].
  split.
  + eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 0 4%N _ _ (F + 0x210) _ HS);
      [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]) | w7_at U32 | | | w7_bnd | lia].
    * apply (w7_mod_val 33 _ t 21); [w7_at A33 | lia | vm_compute; reflexivity | vm_compute; reflexivity].
    * pose proof (Z.mod_pos_bound t 21 ltac:(lia)). w7_bnd.
  + eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 4 4%N _ _ (F + 0x210) _ HS);
      [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]) | w7_at U32 | reflexivity | w7_bnd | w7_bnd | lia].
- (* the trap arm: ~(c + 1) <u 0 is false *)
  w7b_trap Hc A26. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc. lia.
Qed.

(* ======================================== two bytes or more ======================================== *)
Lemma w7b_arm2 : forall t0 s0 r2, w7b_goal (t0 :: s0 :: r2).
Proof using LAWS.
intros t0 s0 r2. unfold w7b_goal.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c Hctx Hregs Hcells Hin Hz.
w7b_pre Hctx Hregs Hcells Hin.
pose proof (Cursor.byte_range t0) as Ht. pose proof (Cursor.byte_range s0) as Hs.
assert (Hlen : Z.of_nat (length (t0 :: s0 :: r2)) = Z.of_nat (length r2) + 2) by (cbn [length]; lia).
rewrite Hlen in H22, H6, Hamr, Hc63, Hra, Hdis.
set (t := bv_unsigned t0) in *. set (s := bv_unsigned s0) in *.
set (nr := Z.of_nat (length r2)) in *.
assert (A9 : ew (Ereg regs (w7b_extra F t s)) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (A26 : ew (Ereg regs (w7b_extra F t s)) 26 = w64 (c - 1))
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (A6 : ew (Ereg regs (w7b_extra F t s)) 6 = w64 (nr + 2 + 1))
  by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
assert (A20 : ew (Ereg regs (w7b_extra F t s)) 20 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (A22 : ew (Ereg regs (w7b_extra F t s)) 22 = w64 (nr + 2))
  by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (A16 : ew (Ereg regs (w7b_extra F t s)) 16 = w64 1)
  by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
assert (A32 : ew (Ereg regs (w7b_extra F t s)) 32 = w64 (F + 0x210)) by exact (ew_Ereg_extra regs _ 0).
assert (A33 : ew (Ereg regs (w7b_extra F t s)) 33 = w64 t) by exact (ew_Ereg_extra regs _ 1).
assert (A34 : ew (Ereg regs (w7b_extra F t s)) 34 = w64 s) by exact (ew_Ereg_extra regs _ 2).
assert (U32 : bv_unsigned (ew (Ereg regs (w7b_extra F t s)) 32) = F + 0x210)
  by (rewrite A32; unfold w64; apply unsigned_lit_small; lia).
assert (Hnr : 0 <= nr) by lia.
assert (D0 := Hdis c ltac:(lia)). assert (D1 := Hdis (c + 1) ltac:(lia)).
assert (HSR : regs_ok (Ereg regs (w7b_extra F t s)) w7b_sr2 regs).
{ unfold w7b_sr2. apply regs_ok_pin.
  - apply regs_ok_Ereg.
  - w7_ne0.
  - rewrite H18. cbn [sv_denot]. rewrite A26. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
assert (HFG : facts_ok (Ereg regs (w7b_extra F t s)) w7b_f2).
{ unfold facts_ok, w7b_f2, w7b_sh20. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I].
  split; [apply (w7_af0 _ _ _ _ _ A20); unfold SHADOW_OFF; lia|].
  split; [apply (w7_af0 _ _ _ _ _ A26); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A22); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A6); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A16); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A33); lia|].
  split; [apply (w7_af0 _ _ _ _ _ A34); lia|].
  exact I. }
pose proof (w7b_entry W memc regs R F c t s 2%nat w7b_sr2 w7b_f2 HSR HFG ltac:(lia) H9 H26
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; apply (proj1 (HFpres (F + 0x210 + o) ltac:(lia)))) V150 V130 V0
  ltac:(apply (rtmb_bytes_field rsegs _ _ _ _ 0%nat 4%nat 0 Hz); [reflexivity | cbn; lia])
  ltac:(apply (rtmb_bytes_field rsegs _ _ _ _ 4%nat 4%nat 0 Hz); [reflexivity | cbn; lia])
  ltac:(intros _; replace (c - 1 + 1) with (c + Z.of_nat 0) by lia;
        exact (rtmb_bytes_byte rsegs _ _ _ _ 0%nat Hbytes ltac:(cbn; lia)))
  ltac:(intros _; replace (c - 1 + 2) with (c + Z.of_nat 1) by lia;
        exact (rtmb_bytes_byte rsegs _ _ _ _ 1%nat Hbytes ltac:(cbn; lia)))
  ltac:(intros a Ha; cbn in Ha; assert (a = c \/ a = c + 1) as [-> | ->] by lia; lia)) as HS.
assert (SHOK : sh_ok rsegs w7b_Bx w7b_SH (Ereg regs (w7b_extra F t s)) (mrestrict (w_H W) memc)).
{ apply (w7b_shok _ lyc Sc W memc mdc F pos _ HAR Hin4 HF).
  - unfold w7b_Bx. apply (U_atom _ 20 SHADOW_OFF A20). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 (F + 0x210) A32). lia. }
assert (HAE : env_agree 32 (Ereg regs (w7b_extra F t s)) (Ereg regs (w7b_extra F t s))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6CB_D7) with (Z_to_bv 64 W6CB_D7).
(* 0x81888 .. the `bltu` 0x81f18: both trap tests of s2 + 1, both checks, e62.type and e62.size stored *)
aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
{ w7b_obl Hra A20 A26. }
{ w7b_obl Hra A20 A26. }
{ eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | exact U32]. }
w7b_ke KE1 W memc F U32 ltac:(intros; reflexivity).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (HAE' : env_agree 32 (Ereg regs (w7b_extra F t s)) Ex) by env_agree_chain HAE end.
pose proof (Z.mod_pos_bound s 12 ltac:(lia)) as Hs12.
(* the `bltu a2, a1`: a2 = s mod 12, a1 = |r| - 2 *)
srr_branch_tok w6cb_tbl_ok HS SHOK w7b_Bspan.
- (* s mod 12 < |r2|: a2 stays *)
  rename Hc into Hlt. rewrite branch_ltu_U in Hlt.
  rewrite (w7_mod_U 34 _ s 12) in Hlt by w7_side A34 A34.
  w7b_Uoff Hlt A6. apply Z.ltb_lt in Hlt.
  (* .. the trap test 0x81f24 *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
  { eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | w7_at U32]. }
  w7b_ke KE2 W memc F U32 ltac:(exact KE1).
  srr_branch_tok w6cb_tbl_ok HS SHOK w7b_Bspan.
  + aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
    { eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | w7_at U32]. }
    w7b_ke KE W memc F U32 ltac:(exact KE2).
    w7_leaf HS HJ KE ltac:(eapply (regs_kept_of_st_ok rsegs _ _ _ regs (w7b_extra F t s) (w_H W) _ HS);
      [env_agree_chain HAE' | vm_compute; reflexivity]).
    cbn [Cursor.fuzz_u8 fst snd]. rewrite Hlen. fold t s nr.
    assert (Hmin : Z.min (s mod 12) nr = s mod 12) by lia. rewrite Hmin.
    split; [w7_reg HS (1%bv : bv 5); reflexivity|].
    split; [w7_reg HS (10%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (11%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A26; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (12%bv : bv 5); apply w7_U_w64; [lia|];
      apply (w7_mod_U 34 _ s 12); w7_side A34 A34|].
    split; [w7_reg HS (22%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (24%bv : bv 5); apply w7_U_w64; [lia|];
      w7_Ueval ltac:(idtac; match goal with |- context [U ?Ex ?A] =>
        lazymatch A with SOff _ _ => fail | SLit _ => fail | _ => idtac end;
        rewrite (w7_mod_U 34 Ex s 12 A) by w7_side A34 A34 end);
      rewrite A6; unfold w64; rewrite unsigned_lit_small by lia; w7_zc; lia|].
    split; [w7_reg HS (26%bv : bv 5); apply w7_U_w64; [lia|];
      w7_Ueval ltac:(idtac; match goal with |- context [U ?Ex ?A] =>
        lazymatch A with SOff _ _ => fail | SLit _ => fail | _ => idtac end;
        rewrite (w7_mod_U 34 Ex s 12 A) by w7_side A34 A34 end);
      rewrite A26; unfold w64; rewrite unsigned_lit_small by lia; w7_zc; lia|].
    split.
    * eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 0 4%N _ _ (F + 0x210) _ HS);
        [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]) | w7_at U32 | | | w7_bnd | lia].
      -- apply (w7_mod_val 33 _ t 21); w7_side A33 A33.
      -- pose proof (Z.mod_pos_bound t 21 ltac:(lia)). w7_bnd.
    * eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 4 4%N _ _ (F + 0x210) _ HS);
        [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]) | w7_at U32 | | | w7_bnd | lia].
      -- apply (w7_mod_val 34 _ s 12); w7_side A34 A34.
      -- w7_bnd.
  + (* the trap arm: ~(c + 2) <u s mod 12 is false *)
    w7b_trap Hc A26. rewrite (w7_mod_U 34 _ s 12) in Hc by w7_side A34 A34. lia.
- (* s mod 12 >= |r2|: a2 := a1 = |r2| *)
  rename Hc into Hge. rewrite branch_ltu_U in Hge.
  rewrite (w7_mod_U 34 _ s 12) in Hge by w7_side A34 A34.
  w7b_Uoff Hge A6. apply Z.ltb_ge in Hge.
  (* .. the trap test 0x81f24 *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
  { eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | w7_at U32]. }
  w7b_ke KE2 W memc F U32 ltac:(exact KE1).
  srr_branch_tok w6cb_tbl_ok HS SHOK w7b_Bspan.
  + aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w7b_Bspan W6CB_CPY.
    { eapply (w7b_awr _ _ _ _ _ _ _ _ _ pos F); [vm_compute; reflexivity | exact Hown | exact HF | w7_at U32]. }
    w7b_ke KE W memc F U32 ltac:(exact KE2).
    w7_leaf HS HJ KE ltac:(eapply (regs_kept_of_st_ok rsegs _ _ _ regs (w7b_extra F t s) (w_H W) _ HS);
      [env_agree_chain HAE' | vm_compute; reflexivity]).
    cbn [Cursor.fuzz_u8 fst snd]. rewrite Hlen. fold t s nr.
    assert (Hmin : Z.min (s mod 12) nr = nr) by lia. rewrite Hmin.
    split; [w7_reg HS (1%bv : bv 5); reflexivity|].
    split; [w7_reg HS (10%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (11%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A26; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (12%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A6; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (22%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite A32; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [w7_reg HS (24%bv : bv 5); cbn [sv_denot]; unfold w64; f_equal; lia|].
    split; [w7_reg HS (26%bv : bv 5); apply w7_U_w64; [lia|];
      rewrite U_SAlu, !U_SOff; cbn [zalu_raw]; rewrite ?ew_ewset_other by lia; rewrite A26, A6; unfold w64;
      rewrite !unsigned_lit_small by lia; w7_zc; lia|].
    split.
    * eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 0 4%N _ _ (F + 0x210) _ HS);
        [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]) | w7_at U32 | | | w7_bnd | lia].
      -- apply (w7_mod_val 33 _ t 21); w7_side A33 A33.
      -- pose proof (Z.mod_pos_bound t 21 ltac:(lia)). w7_bnd.
    * eapply (w7_val_at _ _ (w_H W) _ 0%nat _ 4 4%N _ _ (F + 0x210) _ HS);
        [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]) | w7_at U32 | | | w7_bnd | lia].
      -- apply (w7_mod_val 34 _ s 12); w7_side A34 A34.
      -- w7_bnd.
  + (* the trap arm: ~(c + 2) <u |r2| is false *)
    w7b_trap Hc A26. w7b_Uoff Hc A6. lia.
Qed.
End d.

(* ======================================== the block lemma ======================================== *)
Theorem w6cb_h7 : forall B, w6cb_h7_stmt B.
Proof.
intros B. pose proof (YG0q.AR_laws_ok rsegs B) as LAWS. unfold w6cb_h7_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c r.
destruct r as [|t0 [|s0 r2]].
- exact (w7b_arm0 B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c).
- exact (w7b_arm1 B LAWS t0 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c).
- exact (w7b_arm2 B LAWS t0 s0 r2 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c).
Qed.
End b.

Print Assumptions w6cb_h7.
