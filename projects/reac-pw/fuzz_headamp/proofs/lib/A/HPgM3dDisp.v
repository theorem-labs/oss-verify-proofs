(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the engine run from a fresh entry state and
   its re-seat at a fixed pc) for the value dispatch and the Int arm of reac-pw/fuzz_role's image-A segment M02
   (0x82318 .. 0x823e0). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyI.v at 7e8cf15c304 (the run / branch
   / exit pattern of a value dispatch, the entry state re-seated once the value entry's address is formed) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v at 7e8cf15c304 (m2k_ent_type_slice, m2k_ent_size_slice,
   m2k_ent_word_slice) for reac-pw/fuzz_headamp image A: the m2i_ / m2k_ prefixes are renamed hvd_, every address
   is headamp's own, role's two arms and its MAL exit are replaced by headamp's Bool and Int arms with their five
   exits, and the cuts are lib/A/HPgSegM.v's and lib/A/HPgM3dBase.v's. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the first lane of the piece value_nearest of segment M03 of LLVMFuzzerTestOneInput
   (0x80bc0): lib/A/HPgM3dBase.v's hv_piece_disp_stmt, the walk from VAL 0x83364 to the Float arm FA 0x83430, the
   Int and Float arms' meeting point TAIL 0x83534 and the three segment cuts CELL 0x83548, RFA 0x83454, RF 0x83460.

   proves function LLVMFuzzerTestOneInput (reuse search: at ossv/recipes 2d2ff01bb6f2, read by the released-proof
   index v5 built 2026-10-30T13:16:21Z, no released proof of these pieces; the lookup record is in the PR body).

   THE CODE.
     0x83364 .. 0x83374  a0 := &ent[v] = t6 + 104 v, v = s4 = m + 1 (`li; slli; slli s4; mulhu; add`): hvd_blk1
     0x83378 .. 0x83384  the check of a0 (one shadow entry over [&ent[v], &ent[v] + 16) decides all seven);
     0x83388 `lw a1` = type; 0x83390 `beq a1,6` -> FA; 0x83398 `beq a1,4` -> Int; 0x833a0 `bne a1,2` -> RF
     Bool 0x833a4 .. 0x833e4   `sd a3,0x98(s1)`, size (< 4 -> RF), body word, `snez s4`, `j` CELL
     Int  0x833e8 .. 0x8342c   `sd a3,0x98(s1)`, size (< 4 -> RFA), body word into s4, `bgeu s4,0x100` -> RFA,
                               `j` TAIL
   THE PROOF. Two block lemmas over the machine state, then the cut bookkeeping.
   - hvd_blk1 runs the five address instructions at an entry state with no region and no shadow entry, and hands
     the state at 0x83378 with a0 = &ent[v] and every other register but s4 as at VAL.
   - hvd_blk2 re-enters the engine at 0x83378 with a0 pinned: the real frame's cell R+0x98 as a writable region
     and the value entry's type, size and first body word as a read-only region over three extra atoms; it runs
     and branches to the five exits, each described by hvd_exit.
   - hvd_disp_A takes VAL apart, gets the entry's bytes from the first block (hvd_ent), chains the two blocks, and
     rebuilds each exit cut: hq_base3 by hvd_base3_run (the run writes only R+0x98 .. R+0xa0, above the
     allocator's ceiling), the cut's (location, value) list by hvd_at_carry, and the model side by
     lib/A/HPgM3dVal.v's cell_value and expect_cell lemmas.
   SECTION HYPOTHESES: errno_low : api_env rsegs B (lib/Reusable/YCbq.v: the errno cell lies in the image, below
   kLowMemEnd), for hq_base3's errno clause across the store at R+0x98. MTL : ameter_laws MT is in the Section's
   context; no result here uses it (the runs keep the allocator state, so the meter clause carries as it
   stands). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgCalls HPgSeg HPgSegM HPgM3dVal HPgM3dBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the pcs, the registers, the zone ===================================== *)
Definition HVD_CHK : Z := 0x83378.   (* `srli a1,a0,3`: the check of a0 = &ent[v]; the walk re-enters here *)

(* the registers the address block (0x83364 .. 0x83374) leaves alone: all but a0 and s4 *)
Definition hvd_kept1 : list (bv 5) :=
  map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27;
                   28; 29; 30; 31].
(* the registers the dispatch and the two arms leave alone: all but a0, a1, a2 and s4 *)
Definition hvd_kept : list (bv 5) :=
  map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29;
                   30; 31].

Lemma hvd_kept_sub : forall r, In r hvd_kept -> In r hvd_kept1.
Proof.
intros r Hr. unfold hvd_kept in Hr. apply in_map_iff in Hr as (z & <- & Hz).
unfold hvd_kept1. apply in_map. cbn [In] in Hz |- *. lia.
Qed.

(* the only bytes a run of this lane writes: the param's cell R+0x98 (`sd a3,0x98(s1)`) *)
Definition hvd_wr (cx : hs_scx rsegs) (a : Z) : Prop :=
  e_R (x_e rsegs cx) + 0x98 <= a < e_R (x_e rsegs cx) + 0xa0.

(* ===================================== the value entry's fields ===================================== *)
Lemma hvd_type_slice : forall e, hm_slice (Layout.ent_mem e) 0 4 = Z_to_le_bytes 4 (Model.e_type e).
Proof.
intros e. unfold hm_slice, Layout.ent_mem. cbn [skipn].
change (Z_to_le_bytes 4 (Model.e_type e)) with (Cursor.le32 (Model.e_type e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma hvd_size_slice : forall e, hm_slice (Layout.ent_mem e) 4 4 = Z_to_le_bytes 4 (Model.e_size e).
Proof.
intros e. unfold hm_slice, Layout.ent_mem.
rewrite (Layout.skipn_app_eq (Cursor.le32 (Model.e_type e))) by reflexivity.
change (Z_to_le_bytes 4 (Model.e_size e)) with (Cursor.le32 (Model.e_size e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

(* the body's first four bytes as a field of the entry's 104, for every size: ent_mem pads the body with zeros,
   and trailing zeros do not change a little-endian value *)
Lemma hvd_word_slice : forall e, Model.ent_wf e ->
hm_slice (Layout.ent_mem e) 8 4 = Z_to_le_bytes 4 (Cursor.rd32 (Model.e_body e)).
Proof.
assert (Hzero : forall k, bytes_le_to_Z (repeat Cursor.NUL k) = 0).
{ induction k as [|k IH]; [reflexivity|]. cbn [repeat]. rewrite hm_lez_cons, IH. reflexivity. }
assert (Hpad : forall (l : list byte) (k : nat), bytes_le_to_Z (l ++ repeat Cursor.NUL k) = bytes_le_to_Z l).
{ induction l as [|b l IH]; intros k; [cbn [app]; apply Hzero|].
  cbn [app]. rewrite !hm_lez_cons, IH. reflexivity. }
intros e (_ & Hb & Hs). unfold hm_slice, Layout.ent_mem.
assert (E8 : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
by (intros; reflexivity).
rewrite E8.
assert (Hlen : length (Model.e_body e ++ Cursor.zeros (96 - length (Model.e_body e))) = 96%nat).
{ unfold Cursor.zeros. rewrite length_app, repeat_length. lia. }
assert (Hfr : forall (a : byte) (n k : nat), firstn n (repeat a k) = repeat a (Nat.min n k)).
{ induction n as [|n IH]; intros [|k]; cbn [firstn repeat Nat.min]; try reflexivity. rewrite IH. reflexivity. }
set (X := firstn 4 (Model.e_body e ++ Cursor.zeros (96 - length (Model.e_body e)))).
assert (HX4 : length X = 4%nat) by (subst X; rewrite length_firstn, Hlen; reflexivity).
assert (Hval : bytes_le_to_Z X = Cursor.rd32 (Model.e_body e)).
{ subst X. unfold Cursor.rd32, Cursor.zeros. rewrite firstn_app, Hfr. apply Hpad. }
rewrite <- Hval, <- HX4. symmetry. apply YA0d.Z_to_le_bytes_to_Z.
Qed.

(* what hm_pp_ent asks of a record *)
Lemma hvd_pp_ok : forall r, Model.pod_rec_wf r ->
Z.of_nat (length (Model.buf r)) <= Layout.POD_BUF_MAX /\
Forall (fun e => (length (Model.e_body e) <= 96)%nat) (Model.ents r).
Proof.
intros r Hw. split.
- pose proof Hw as (Hs & Hk & He & Hl & HL & Hc). unfold Model.buf. destruct (Model.p_corr r) as [[off bs]|].
  + destruct Hc as (Ho & Hb & _). unfold Model.overwrite. rewrite !length_app, length_firstn, length_skipn.
    unfold Layout.POD_BUF_MAX. lia.
  + unfold Layout.POD_BUF_MAX. lia.
- pose proof (Model.ents_wf r Hw) as [_ HF]. eapply Forall_impl; [|exact HF]. intros e (_ & Hb & Hs).
  cbv beta. lia.
Qed.

(* ===================================== the value language ===================================== *)
Lemma hvd_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the word an `lw` leaves, as HPgM3dVal.hvm_sx *)
Lemma hvd_U_sx : forall E (n : nat) (v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SExt true 32 (SOff n 0)) = hvm_sx v.
Proof. intros E n v H Hv. rewrite (hv_U_sext32 E n v H Hv). reflexivity. Qed.

(* `snez s4,a0` of the Bool arm: sltu s4,zero,a0 *)
Lemma hvd_U_snez : forall E (n : nat) (v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SAlu ALU_SLTU (SLit 0) (SExt true 32 (SOff n 0))) = (if v =? 0 then 0 else 1).
Proof.
intros E n v H Hv. rewrite U_SAlu, (hvd_U_sx E n v H Hv), U_SLit. change (zcanon 0) with 0.
pose proof (hvm_sx_range v Hv) as Hr. pose proof (hvm_sx_zero v Hv) as Hz.
cbn [zalu_raw]. destruct (Z.eqb_spec v 0) as [E0|E0].
- rewrite (proj2 Hz E0). reflexivity.
- assert (Hq : 0 < hvm_sx v).
  { destruct (Z.eq_dec (hvm_sx v) 0) as [Q|Q]; [|lia]. exfalso. apply E0. apply Hz. exact Q. }
  rewrite (proj2 (Z.ltb_lt 0 (hvm_sx v)) Hq). reflexivity.
Qed.

Ltac hvd_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Ltac hvd_io := let rec k := first [apply same_io_refl | eapply same_io_trans; [| apply hv_same_io_wvb]; k] in k.

(* ===================================== the two blocks over the machine state ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- 0x83364 .. 0x83374: the address of the value entry ---- *)
Definition hvd_post1 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (A : Z) :
world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HVD_CHK) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r, In r hvd_kept1 -> getr regs2 r = getr regs r) /\ getr regs2 (Z_to_bv 5 10) = w64 A.

Lemma hvd_blk1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 20) = w64 i -> getr regs (Z_to_bv 5 31) = w64 b ->
0 <= i <= 32 -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs HV_VAL regs memc mdc)
  (hvd_post1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (b + 104 * i)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i b HJ H20 H31 Hi Hb Hs.
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E20 : ew (Ereg regs []) 20 = Z_to_bv 64 i)
  by (rewrite (ew_Ereg_nat regs [] 20 (Z_to_bv 5 20) eq_refl), H20; reflexivity).
assert (E31 : ew (Ereg regs []) 31 = Z_to_bv 64 b)
  by (rewrite (ew_Ereg_nat regs [] 31 (Z_to_bv 5 31) eq_refl), H31; reflexivity).
assert (HG : facts_ok (Ereg regs []) (mkFacts [] [] [])).
{ split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (hv_entry HV_VAL [] [] (mkFacts [] [] []) W regs [] memc (Forall_nil _) eq_refl (Forall_nil _) I HG)
  as HS.
assert (SHOK : sh_ok rsegs HV_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 HV_VAL) with (Z_to_bv 64 HV_VAL).
hv_run_to hv_awr HVD_CHK.
pose proof (frame_of_read_only E [] memc (ms_mem ms) eq_refl HF) as HM.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E _ ms HS eq_refl) at 1; rewrite HM; reflexivity|].
split; [rewrite HM in HJ; exact HJ|].
split; [apply hv_same_io_wvb|].
split.
{ intros r Hr. exact (regs_kept_of_st_ok rsegs E _ _ regs [] hvd_kept1 HS HAE ltac:(vm_compute; reflexivity) r Hr). }
rewrite (st_ok_restrict_reg rsegs (w_H W) E _ ms _ HS).
hvd_sv. exact (hv_denot_a0 E 20 31 i b E20 Hi E31 Hb Hs).
Qed.

(* ---- 0x83378 .. : the dispatch and the Bool and Int arms, to the five exits ---- *)
(* t, s, bw: the value entry's type, size and first body word; p the param in a3; R = s1 *)
Definition hvd_exit (R p t s bw : Z) (regs : bvmap 5 word) (H : word -> bool) (pc : Z) (regs2 : bvmap 5 word)
(mem2 : word -> option byte) : Prop :=
(pc = HV_FLT /\ t = Model.POD_FLOAT /\ getr regs2 (Z_to_bv 5 10) = getr regs (Z_to_bv 5 10)) \/
(pc = HV_RF /\ ((t <> Model.POD_BOOL /\ t <> Model.POD_INT /\ t <> Model.POD_FLOAT) \/
                (t = Model.POD_BOOL /\ s < 4))) \/
(pc = HV_RFA /\ t = Model.POD_INT /\ (s < 4 \/ (4 <= s /\ 255 < bw))) \/
(pc = HV_TAIL /\ t = Model.POD_INT /\ 4 <= s /\ bw <= 255 /\ getr regs2 (Z_to_bv 5 20) = w64 bw /\
 val_mem rsegs (mrestrict H mem2) (R + 0x98) 8 (p mod 2 ^ 64)) \/
(pc = HV_CELL /\ t = Model.POD_BOOL /\ 4 <= s /\ getr regs2 (Z_to_bv 5 20) = w64 (if bw =? 0 then 0 else 1) /\
 val_mem rsegs (mrestrict H mem2) (R + 0x98) 8 (p mod 2 ^ 64)).

Definition hvd_post2 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (R p t s bw : Z) :
world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists pc regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r hvd_kept -> getr regs2 r = getr regs r) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (R + 0x98 <= x < R + 0xa0) ->
 aview rsegs (w_H W) mem2 x = aview rsegs (w_H W) memc x) /\
hvd_exit R p t s bw regs (w_H W) pc regs2 mem2.

(* the state at an exit: the post's first five clauses *)
Ltac hvd_out pc :=
apply SRr_ret; split; [reflexivity|];
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms), HAE : env_agree 32 _ ?E,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?md _, KE : forall a, _ -> ~ _ -> _ = _ |- _ =>
exists pc, (ms_regs ms), (ms_mem ms), md;
split; [rewrite (st_ok_restrict_mkst rsegs _ E ss ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [hvd_io|];
split; [intros r0 Hr0;
        exact (regs_kept_of_st_ok rsegs _ _ _ _ _ hvd_kept HS HAE ltac:(vm_compute; reflexivity) r0 Hr0)|];
split; [exact KE|]
end.

(* the param's cell R+0x98 at an exit after `sd a3,0x98(s1)`: the frame region's one chunk *)
Ltac hvd_cell98 E9 D13 Hp :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- val_mem _ _ _ _ _ =>
  let Hok := fresh "Hok" in let Hfr := fresh "Hfr" in let Hch := fresh "Hch" in let Hc := fresh "Hc" in
  let V := fresh "V" in
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _);
  cbn [ss_mem] in Hok; apply Forall_cons_iff in Hok as [Hfr _];
  destruct Hfr as (_ & _ & _ & Hch); cbn [YP09.r_chunks] in Hch;
  apply Forall_cons_iff in Hch as [Hc _];
  pose proof (val_of_chunk_ok rsegs E _ _ 152 8%N (SOff 13 0) _ Hc D13 ltac:(cbn; lia) ltac:(cbn; lia)) as V;
  cbn [base_val YP09.r_base] in V; rewrite E9 in V;
  rewrite Z.mod_small by lia; exact V
end.

Lemma hvd_blk2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R a p t s bw : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
getr regs (Z_to_bv 5 10) = w64 a -> getr regs (Z_to_bv 5 13) = w64 p ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> sp0 - STK <= R -> R + 0xa0 <= sp0 ->
4096 <= a -> a + 16 <= R -> a <= 0x7fffff800000 ->
(a + 16 <= kLowShadowBeg \/ kHighMemBeg <= a) ->
0 <= p < 2 ^ 64 -> 0 <= t < 2 ^ 32 -> 0 <= s <= 45 -> 0 <= bw < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) memc) a 4 t ->
val_mem rsegs (mrestrict (w_H W) memc) (a + 4) 4 s ->
val_mem rsegs (mrestrict (w_H W) memc) (a + 8) 4 bw ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF a 16 ->
SRr rsegs W (cfg_at rsegs HVD_CHK regs memc mdc)
  (hvd_post2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R p t s bw).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R a p t s bw
  HJ H9 H23 H10 H13 HR HR16 Hw1 Hw2 Ha0 Ha1 Ha2 Happ Hp Ht Hs Hbw Vt Vs Vb Hra.
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
set (ex := [w64 t; w64 s; w64 bw] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ rewrite (ew_Ereg_nat regs ex 9 (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : bv_unsigned (ew (Ereg regs ex) 10) = a).
{ rewrite (ew_Ereg_nat regs ex 10 (Z_to_bv 5 10) eq_refl), H10. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs ex 23 (Z_to_bv 5 23) eq_refl), H23. reflexivity. }
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 p).
{ rewrite (ew_Ereg_nat regs ex 13 (Z_to_bv 5 13) eq_refl), H13. reflexivity. }
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 t)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 s)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 bw)
  by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
pose (rgs := [hv_frame 0x98 0xa0 0x98 0xa0 []; hv_ent (SOff 32 0) (SOff 33 0) (SOff 34 0)]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs ex) (mrestrict (w_H W) memc)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (hv_frame_ok _ W memc R STK sp0 0x98 0xa0 0x98 0xa0 [] E9); [lia | lia | exact Hpres | intros _; lia |].
    apply Forall_nil.
  - apply (hv_ent_ok _ W memc a _ _ _ t s bw E10); try lia;
      [rewrite hvd_denot0; exact E32 | rewrite hvd_denot0; exact E33 | rewrite hvd_denot0; exact E34
      | exact Vt | exact Vs | exact Vb]. }
assert (Hwf : regions_wf rgs = true) by (vm_compute; reflexivity).
assert (Hpd : pairwise_disjoint (Ereg regs ex) rgs).
{ cbn [pairwise_disjoint all_disjoint rgs]. split; [|split; exact I]. split; [|exact I].
  unfold extent_disjoint, hv_frame, hv_ent. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E10. right. lia. }
assert (HG : facts_ok (Ereg regs ex) hv_facts10).
{ apply (hv_facts10_ok _ R a E9 HR HR16); [| exact E10 | lia].
  rewrite E23. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
pose proof (hv_entry HVD_CHK [] rgs hv_facts10 W regs ex memc (Forall_nil _) Hwf Hrs Hpd HG) as HS.
assert (SHOK : sh_ok rsegs HV_Bx hv_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hv_sh_ok W memc (Ereg regs ex) a); [| | exact Hra | exact Happ].
  - unfold HV_Bx. apply (hv_U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - apply (hv_U_atom _ 10 a); [|lia]. apply bv_eq. rewrite E10. symmetry. apply unsigned_lit_small. lia. }
assert (D13 : sv_denot (Ereg regs ex) (SOff 13 0) = Z_to_bv 64 p) by (rewrite hvd_denot0; exact E13).
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE.
assert (KE : forall x, 0 <= x < 2 ^ 64 -> ~ (R + 0x98 <= x < R + 0xa0) ->
  aview rsegs (w_H W) memc x = aview rsegs (w_H W) memc x) by (intros; reflexivity).
unfold cfg_at. change (w64 HVD_CHK) with (Z_to_bv 64 HVD_CHK).
(* 0x83378 .. 0x8338c, to `beq a1,a2` 0x83390 with a1 the type *)
hv_run hv_awr. hv_keep hv_kwr.
hv_branch Hb.
all: rewrite branch_eq_U, (hvd_U_sx E 32 t E32 Ht), U_lit in Hb by lia.
- (* the type is 6: the Float arm FA 0x83430 *)
  apply Z.eqb_eq in Hb. apply (hvm_sx_eq t 6 Ht ltac:(lia)) in Hb.
  hv_run_to hv_awr HV_FLT. hv_keep hv_kwr.
  hvd_out HV_FLT.
  left. split; [reflexivity|]. split; [exact Hb|].
  exact (regs_kept_of_st_ok rsegs _ _ _ _ _ [Z_to_bv 5 10] HS HAE ltac:(vm_compute; reflexivity) (Z_to_bv 5 10)
           ltac:(left; reflexivity)).
- apply Z.eqb_neq in Hb. assert (Ht6 : t <> 6) by (intros Hc; apply Hb; apply (hvm_sx_eq t 6 Ht ltac:(lia)); exact Hc).
  hv_run hv_awr. hv_keep hv_kwr.
  hv_branch Hb2.
  all: rewrite branch_eq_U, (hvd_U_sx E 32 t E32 Ht), U_lit in Hb2 by lia.
  + (* the type is 4: the Int arm 0x833e8 *)
    apply Z.eqb_eq in Hb2. apply (hvm_sx_eq t 4 Ht ltac:(lia)) in Hb2.
    hv_run hv_awr. hv_keep hv_kwr.
    hv_branch Hb3.
    all: rewrite branch_ltu_U, (hvd_U_sx E 33 s E33 ltac:(lia)), U_lit, (hvm_sx_id s ltac:(lia)) in Hb3 by lia.
    * (* the size is below 4: RFA *)
      apply Z.ltb_lt in Hb3.
      hv_run_to hv_awr HV_RFA. hv_keep hv_kwr.
      hvd_out HV_RFA.
      right; right; left. split; [reflexivity|]. split; [exact Hb2|]. left; exact Hb3.
    * apply Z.ltb_ge in Hb3.
      hv_run hv_awr. hv_keep hv_kwr.
      hv_branch Hb4.
      all: rewrite branch_geu_U, (hvd_U_sx E 34 bw E34 Hbw), U_lit in Hb4 by lia.
      -- (* the value is 256 or more: RFA *)
         apply negb_true_iff, Z.ltb_ge in Hb4. apply (proj1 (hvm_sx_256 bw Hbw)) in Hb4.
         hv_run_to hv_awr HV_RFA. hv_keep hv_kwr.
         hvd_out HV_RFA.
         right; right; left. split; [reflexivity|]. split; [exact Hb2|]. right; split; [exact Hb3 | exact Hb4].
      -- (* the value is below 256: TAIL *)
         apply negb_false_iff, Z.ltb_lt in Hb4.
         assert (Hb5 : bw <= 255) by (destruct (Z.le_gt_cases bw 255) as [L|L]; [exact L|];
           apply (proj2 (hvm_sx_256 bw Hbw)) in L; lia).
         hv_run_to hv_awr HV_TAIL. hv_keep hv_kwr.
         hvd_out HV_TAIL.
         right; right; right; left. split; [reflexivity|]. split; [exact Hb2|]. split; [exact Hb3|].
         split; [exact Hb5|]. split.
         ++ rewrite (st_ok_restrict_reg rsegs _ E _ _ _ HS). hvd_sv.
            rewrite denot_lit_U, (hvd_U_sx E 34 bw E34 Hbw), (hvm_sx_id bw ltac:(lia)). reflexivity.
         ++ hvd_cell98 E9 D13 Hp.
  + apply Z.eqb_neq in Hb2. assert (Ht4 : t <> 4) by (intros Hc; apply Hb2; apply (hvm_sx_eq t 4 Ht ltac:(lia)); exact Hc).
    hv_run hv_awr. hv_keep hv_kwr.
    hv_branch Hb3.
    all: rewrite branch_ne_U, (hvd_U_sx E 32 t E32 Ht), U_lit in Hb3 by lia.
    * (* the type is not 2: RF *)
      apply negb_true_iff, Z.eqb_neq in Hb3.
      assert (Ht2 : t <> 2) by (intros Hc; apply Hb3; apply (hvm_sx_eq t 2 Ht ltac:(lia)); exact Hc).
      hv_run_to hv_awr HV_RF. hv_keep hv_kwr.
      hvd_out HV_RF.
      right; left. split; [reflexivity|]. left. unfold Model.POD_BOOL, Model.POD_INT, Model.POD_FLOAT.
      split; [exact Ht2|]. split; [exact Ht4 | exact Ht6].
    * (* the type is 2: the Bool arm 0x833a4 *)
      apply negb_false_iff, Z.eqb_eq in Hb3. apply (hvm_sx_eq t 2 Ht ltac:(lia)) in Hb3.
      hv_run hv_awr. hv_keep hv_kwr.
      hv_branch Hb4.
      all: rewrite branch_ltu_U, (hvd_U_sx E 33 s E33 ltac:(lia)), U_lit, (hvm_sx_id s ltac:(lia)) in Hb4 by lia.
      -- (* the size is below 4: RF *)
         apply Z.ltb_lt in Hb4.
         hv_run_to hv_awr HV_RF. hv_keep hv_kwr.
         hvd_out HV_RF.
         right; left. split; [reflexivity|]. right. split; [exact Hb3 | exact Hb4].
      -- (* `snez s4,a0` and CELL *)
         apply Z.ltb_ge in Hb4.
         hv_run_to hv_awr HV_CELL. hv_keep hv_kwr.
         hvd_out HV_CELL.
         right; right; right; right. split; [reflexivity|]. split; [exact Hb3|]. split; [exact Hb4|]. split.
         ++ rewrite (st_ok_restrict_reg rsegs _ E _ _ _ HS). hvd_sv.
            rewrite denot_lit_U, (hvd_U_snez E 34 bw E34 Hbw). reflexivity.
         ++ hvd_cell98 E9 D13 Hp.
Qed.

End k.

(* ===================================== the cut lists ===================================== *)
(* the VAL cut's facts this lane carries to every exit: all but s4 = m + 1 *)
Definition hvd_L (cx : hs_scx rsegs) (r : Model.pod_rec) (m : nat) (ch p : Z) : list (hd_loc * Z) :=
  hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++
  [(LReg 31, e_pp (x_e rsegs cx) + HQ_ENT0); (LReg 7, hq_nent r); (LReg 13, p); (LReg 18, hvm_top p);
   (LReg 21, Z.of_nat m + 2); (LReg 28, Headamp.REFUSE_OUT_OF_RANGE); (LCell XR 0xa0, ch)].

(* a location the runs of this lane keep: a register of kept, or a real-frame cell apart from R+0x98 *)
Definition hvd_locb (kept : list (bv 5)) (f : hd_loc * Z) : bool :=
match fst f with
| LReg r => existsb (fun c => bv_eqb c (Z_to_bv 5 r)) kept
| LCell XR o => ((o + 8 <=? 0x98) || (0xa0 <=? o)) && (0 <=? o) && (o <=? 0x1f0)
| LCell _ _ => false
end.

Ltac hvd_unf := unfold hvd_L, hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body.
Ltac hvd_in := hvd_unf; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac hvd_kin := apply in_map; cbn [In]; lia.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

Lemma hvd_at_sub : forall H mem regs e L L', hs_at rsegs H mem regs e L -> (forall x, In x L' -> In x L) ->
hs_at rsegs H mem regs e L'.
Proof.
intros H mem regs e L L' HL Hs. unfold hs_at in *. rewrite Forall_forall in *. intros x Hx. exact (HL x (Hs x Hx)).
Qed.

Lemma hvd_at_get : forall H mem regs e L r v, hs_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.

(* a list of facts that is a sub-list of a hypothesis' *)
Ltac hvd_sub HL :=
apply (hvd_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; hvd_unf; cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.

(* a cut's facts across a run of this lane: the registers of kept, and the cells apart from R+0x98 *)
Lemma hvd_at_carry : forall (cx : hs_scx rsegs) (W : world rsegs) mem mem' regs regs' (kept : list (bv 5)) L,
hs_at rsegs (w_H W) mem regs (x_e rsegs cx) L ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvd_wr cx a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
(forall r, In r kept -> getr regs' r = getr regs r) ->
forallb (hvd_locb kept) L = true ->
0 <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) + 0x200 <= 2 ^ 64 ->
hs_at rsegs (w_H W) mem' regs' (x_e rsegs cx) L.
Proof.
intros cx W mem mem' regs regs' kept L HAT HK Hk Hb HR0 HR1.
unfold hs_at in *.
apply (hm_atl_kept rsegs (w_H W) mem (w_H W) mem' regs regs' (x_e rsegs cx) L HAT).
intros f Hf. pose proof (proj1 (forallb_forall _ _) Hb f Hf) as Hl.
apply (hm_keeps_of rsegs (fun a => ~ (0 <= a < 2 ^ 64) \/ hvd_wr cx a)).
- intros x Hx. apply HK.
  + destruct (Z.le_gt_cases 0 x); destruct (Z.lt_ge_cases x (2 ^ 64)); try lia;
    exfalso; apply Hx; left; lia.
  + intros Hw. apply Hx. right. exact Hw.
- unfold hvd_locb in Hl. destruct f as [[rr|bb o] v]; cbn [fst] in Hl |- *.
  + apply existsb_exists in Hl as (c & Hc & Hcb). apply bv_eqb_eq in Hcb. subst c. exact (Hk _ Hc).
  + destruct bb; try discriminate Hl.
    apply andb_prop in Hl as [Hl Ho2]. apply andb_prop in Hl as [Hl Ho1].
    apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
    intros i Hi [Hn|Hw]; [apply Hn; cbn [hd_xv]; lia|]. unfold hvd_wr in Hw. cbn [hd_xv] in Hw.
    apply orb_prop in Hl as [Hl|Hl]; apply Z.leb_le in Hl; lia.
Qed.

(* the frame object x across a run of this lane: it lies below the allocator's ceiling *)
Lemma hvd_x_kept : forall (cx : hs_scx rsegs) (W : world rsegs) mem mem' cs keys rf,
hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
hq_x_at rsegs cx W mem cs keys rf ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvd_wr cx a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
hq_x_at rsegs cx W mem' cs keys rf.
Proof.
intros cx W mem mem' cs keys rf Hpre (Hg & Hl & Hrest) HK. split; [|split; [exact Hl | exact Hrest]].
destruct (hv_stack B cx _ Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
destruct (hv_apart B cx _ Hpre) as (_ & _ & _ & _ & HF0 & HFc & _).
apply (proj1 (hm_bytes_zbytes rsegs (w_H W) mem' _ _)).
apply (hm_bytes_kept rsegs (w_H W) mem); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W) mem _ _) Hg)|].
rewrite (hq_x_open_len cs keys rf Hl). intros y Hy.
unfold hvd_wr, HQ_XO, T_SEG_STK, ASTACK in *. apply HK; lia.
Qed.

(* hs_core across a run that writes at most R+0x98 .. R+0xa0, which lies in M03's write set (R .. R+0x120) *)
Lemma hvd_core_run : forall (cx : hs_scx rsegs) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvd_wr cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcore HJ3 Hio3 H234 HK.
unfold hs_core, hs_mid in Hcore |- *.
destruct Hcore as (_ & Hr234 & Hfr & Hperm & Hio & Hmo & Hmem).
split; [exact HJ3|].
split; [intros q Hq; rewrite (H234 q Hq); exact (Hr234 q Hq)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo|].
intros a Ha Hs He. rewrite (HK a Ha); [exact (Hmem a Ha Hs He)|].
intros Hw. apply He. unfold hq_E3. left. unfold hd_inw. cbn [hi_w3 headamp_himg_A].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv].
unfold hvd_wr in Hw. lia.
Qed.

(* what every cut inside M03 carries, across a run of this lane *)
Lemma hvd_base3_run : forall (cx : hs_scx rsegs) r ev (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvd_wr cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HJ3 Hio3 H234 HK.
pose proof HS as (Hpre & _ & Hwf & Hlen & _ & _ & Hpodb & _ & _ & _ & _ & Houtb & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
destruct (hv_stack B cx _ Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
destruct (hv_apart B cx _ Hpre) as (_ & Hpp0 & Hppc & _ & HF0 & HFc & _).
destruct Hpodb as (_ & Hpodin & _). destruct Houtb as (_ & Houtin & _).
destruct (hv_blk_low B cx _ _ _ Hpre Hpodin) as (_ & Hpod0 & Hpodc).
destruct (hv_blk_low B cx _ _ _ Hpre Houtin) as (_ & Hout0 & Houtc).
pose proof (@alloc_ceiling_value rc) as ((Hc0 & Hc1) & _).
unfold T_SEG_STK, ASTACK in Hceil.
assert (KL : forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply HK; [lia|]. unfold hvd_wr. lia. }
assert (Hreq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct Hb as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & (ev2 & Herr)).
split; [exact (hvd_core_run cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcore HJ3 Hio3 H234 HK)|].
split; [exact Hfxk|].
split.
{ unfold hs_fsh_at in *. apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ _ Hfsh).
  intros i Hi. rewrite hq_shX_len in Hi. apply KL. unfold shadow_addr, SHADOW_OFF.
  assert (Hd0 : 0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : e_F (x_e rsegs cx) / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  lia. }
split.
{ apply (hm_rom_kept rsegs W2 W2 mem2 mem3 Hrom). intros a (sg & Hin & _ & Hsb).
  assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hin | exact Hsb]).
  pose proof (hv_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow. apply KL. lia. }
split.
{ unfold hs_pp_at in *. apply (proj1 (hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hpp)|].
  rewrite (Layout.length_pp_bytes r Hwf). intros x Hx. apply KL. lia. }
split.
{ apply (proj1 (hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hpod)|].
  rewrite <- Hlen. intros x Hx. pose proof (Hreq (e_len (x_e rsegs cx)) ltac:(lia)). apply KL. lia. }
split.
{ apply (proj1 (hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hout)|].
  pose proof (Headamp.parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx))
    ltac:(lia)) as Hok.
  fold (hq_ans rsegs cx r) in Hok.
  apply answer_ok_parts in Hok as (Hcase & _).
  assert (Hlc : Z.of_nat (length (ans_cells (hq_ans rsegs cx r))) <= e_cap (x_e rsegs cx))
    by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
  rewrite length_ha_cells_bytes. intros x Hx.
  pose proof (Hreq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)). apply KL. lia. }
split.
{ apply (proj1 (hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hres)|].
  unfold ans_res_bytes. rewrite length_ha_res_bytes. intros x Hx. apply KL. unfold HQ_RES in Hx. lia. }
exists ev2. intros j Hj.
assert (Hj' : 0 <= Z.of_nat j < 4) by lia.
pose proof (hv_errno_low B errno_low (Z.of_nat j) Hj') as He.
rewrite (KL _ He). exact (Herr j Hj).
Qed.

(* the value entry ent[m + 1] in the first block: its three words, its shadow, its place *)
Lemma hvd_ent : forall (cx : hs_scx rsegs) r ev (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 ->
hq_pair_inv rsegs cx r m k v cs keys rf ->
Model.ent_wf v /\ (S m < 32)%nat /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hv_entA cx m) 4 (Model.e_type v) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hv_entA cx m + 4) 4 (Model.e_size v) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hv_entA cx m + 8) 4 (Cursor.rd32 (Model.e_body v)) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hv_entA cx m) 16 /\
4096 <= hv_entA cx m /\ hv_entA cx m + 16 <= alloc_ceiling /\
(hv_entA cx m + 16 <= kLowShadowBeg \/ kHighMemBeg <= hv_entA cx m).
Proof.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf HS Hb (Hv & _ & HSm & _).
pose proof HS as (Hpre & _ & Hwf & _).
destruct (hv_apart B cx _ Hpre) as (Hppin & Hpp0 & Hppc & Happ & _).
destruct Hb as (Hcore & _ & _ & _ & Hpp & _).
destruct Hcore as (HJ & _ & _ & Hperm & _).
pose proof HJ as (HAR & _).
pose proof (Model.ents_wf r Hwf) as (Hn32 & Hall).
assert (Hvwf : Model.ent_wf v) by (rewrite Hv; apply (proj1 (Forall_forall _ _) Hall); apply nth_In; exact HSm).
destruct (hvd_pp_ok r Hwf) as (Hbm & Hbod).
assert (Hent : hm_bytes rsegs (w_H W2) mem2 (hv_entA cx m) (Layout.ent_mem v)).
{ unfold hs_pp_at in Hpp. apply (proj2 (hm_bytes_zbytes rsegs _ _ _ _)) in Hpp. unfold Layout.pp_bytes in Hpp.
  pose proof (hm_pp_ent rsegs _ _ _ _ _ _ Hbm Hn32 Hbod _ _ _ (S m) Hpp HSm) as He. rewrite <- Hv in He.
  replace (hv_entA cx m) with (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (S m)))
    by (unfold hv_entA, HQ_ENT0, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
  exact He. }
assert (Hlen : length (Layout.ent_mem v) = 104%nat)
  by (apply Layout.length_ent_mem; destruct Hvwf as (_ & Hbl & Hz); lia).
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
unfold Layout.PP_SIZE in Hppc, Happ, Hreq.
split; [exact Hvwf|]. split; [lia|].
split.
{ pose proof (hm_bytes_field rsegs _ _ _ _ 0 4 _ Hent (hvd_type_slice v) ltac:(lia)) as X.
  change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
split.
{ pose proof (hm_bytes_field rsegs _ _ _ _ 4 4 _ Hent (hvd_size_slice v) ltac:(lia)) as X.
  change (Z.of_nat 4) with 4 in X. exact X. }
split.
{ pose proof (hm_bytes_field rsegs _ _ _ _ 8 4 _ Hent (hvd_word_slice v Hvwf) ltac:(lia)) as X.
  change (Z.of_nat 8) with 8 in X. exact X. }
split.
{ destruct (hm_blk_ra rsegs B ly2 S2 W2 mem2 md2 _ _ (hv_entA cx m) 16 HAR
    (Permutation_in _ (Permutation_sym Hperm) Hppin)) as (Hra & _);
  [unfold hv_entA, HQ_ENT0; lia | unfold Layout.PP_SIZE; rewrite Hreq; unfold hv_entA, HQ_ENT0; lia | exact Hra]. }
unfold hv_entA, HQ_ENT0. lia.
Qed.

(* ===================================== the lane ===================================== *)
Theorem hvd_disp_A : hv_piece_disp_stmt B MT.
Proof.
unfold hv_piece_disp_stmt.
intros cx POST r ev at0 m HS HCELL HRF HRFA HTAIL HFA.
unfold hq_from_VAL. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf Hcut.
destruct Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & Hm & Hkey & Hpair & Hcs & Hx).
pose proof HS as (Hpre & _).
destruct (hv_stack B cx _ Hpre) as (HspR & HR32 & Hrsz & Hwin & Hceil & H46 & Hsp47 & _ & _ & _ & _).
destruct (hv_apart B cx _ Hpre) as (_ & Hpp0 & Hppc & _ & HF0 & HFc & _ & _).
pose proof (@alloc_ceiling_value rc) as ((Hc0 & Hc1) & _).
unfold T_SEG_STK, ASTACK in Hwin, Hceil. unfold Layout.PP_SIZE in Hppc.
assert (HR16 : e_R (x_e rsegs cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact HR32]]. }
destruct (hvd_ent cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf HS Hb3 Hpair)
  as (Hvwf & Hm32 & Vt & Vs & Vb & Hra & Ha0 & Ha1 & Happ).
destruct (hvm_ent_bounds v Hvwf) as (Ht & Hsz).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbw.
destruct (hvm_key_cell _ ch p Hkey) as (Hch & Hp).
assert (Hpr : 0 <= p < 2 ^ 64) by (unfold HA_PHANTOM, HA_PAD, HA_SENS in Hp; lia).
pose proof Hb3 as ((HJ & _) & _).
unfold hs_at_cx in Hat.
pose proof (hvd_at_get _ _ _ _ _ 9 (e_R (x_e rsegs cx)) Hat ltac:(hvd_in)) as R9.
pose proof (hvd_at_get _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(hvd_in)) as R23.
pose proof (hvd_at_get _ _ _ _ _ 20 (Z.of_nat m + 1) Hat ltac:(hvd_in)) as R20.
pose proof (hvd_at_get _ _ _ _ _ 31 (e_pp (x_e rsegs cx) + HQ_ENT0) Hat ltac:(hvd_in)) as R31.
pose proof (hvd_at_get _ _ _ _ _ 13 p Hat ltac:(hvd_in)) as R13.
assert (HatV : hs_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (hvd_L cx r m ch p)) by hvd_sub Hat.
(* 0x83364 .. 0x83374 *)
eapply SRr_bind.
{ exact (hvd_blk1 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (Z.of_nat m + 1)
    (e_pp (x_e rsegs cx) + HQ_ENT0) HJ R20 R31 ltac:(lia) ltac:(unfold HQ_ENT0; lia)
    ltac:(unfold HQ_ENT0; lia)). }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & H10).
assert (Q9 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
  by (rewrite Hk3; [exact R9 | unfold hvd_kept1; hvd_kin]).
assert (Q23 : getr regs3 (Z_to_bv 5 23) = w64 SHADOW_OFF)
  by (rewrite Hk3; [exact R23 | unfold hvd_kept1; hvd_kin]).
assert (Q13 : getr regs3 (Z_to_bv 5 13) = w64 p)
  by (rewrite Hk3; [exact R13 | unfold hvd_kept1; hvd_kin]).
(* 0x83378 .. the five exits *)
eapply SRr_bind.
{ exact (hvd_blk2 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e rsegs cx)) (hv_entA cx m) p
    (Model.e_type v) (Model.e_size v) (Cursor.rd32 (Model.e_body v)) HJ3 Q9 Q23 H10 Q13
    ltac:(lia) HR16 ltac:(lia) ltac:(lia) Ha0 ltac:(lia) ltac:(lia) Happ Hpr Ht Hsz Hbw Vt Vs Vb Hra). }
intros W4 c4 _ (-> & pc & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & KE & Hexit).
assert (Hk : forall r0, In r0 hvd_kept -> getr regs4 r0 = getr regs2 r0)
  by (intros r0 Hr0; rewrite (Hk4 r0 Hr0); exact (Hk3 r0 (hvd_kept_sub r0 Hr0))).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ hvd_wr cx a ->
  aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a) by (intros a Ha Hw; exact (KE a Ha Hw)).
assert (H234 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs4 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)).
{ intros q Hq. apply Hk. destruct Hq as [-> | [-> | ->]]; unfold hvd_kept; hvd_kin. }
assert (Hio : same_io md2 md4) by exact (same_io_trans _ _ _ Hio3 Hio4).
pose proof (hvd_base3_run cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HS Hb3 HJ4 Hio H234 HK) as Hb4.
assert (HatC : hs_at rsegs (w_H W2) mem4 regs4 (x_e rsegs cx) (hvd_L cx r m ch p)).
{ apply (hvd_at_carry cx W2 mem2 mem4 regs2 regs4 hvd_kept _ HatV HK Hk ltac:(vm_compute; reflexivity)); lia. }
pose proof (hvd_x_kept cx W2 mem2 mem4 cs (keys + 1) rf Hpre Hx HK) as Hx4.
assert (KB : forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a)
  by (intros a Ha; apply HK; [lia | unfold hvd_wr; lia]).
unfold hvd_exit in Hexit.
destruct Hexit as [(-> & Ht6 & H10') | [(-> & Hrf) | [(-> & Ht4 & Hrfa) |
  [(-> & Ht4 & Hs4 & Hbw' & H20 & V98) | (-> & Ht2 & Hs4 & H20 & V98)]]]].
- (* FA: the type is Float *)
  apply (HFA fx2 ly2 S2 W2 regs4 mem4 md4 k v ch p cs keys rf).
  split; [exact Hb4|].
  split.
  { assert (HatF : hs_at rsegs (w_H W2) mem4 regs4 (x_e rsegs cx) ((LReg 10, hv_entA cx m) :: hvd_L cx r m ch p)).
    { apply Forall_cons; [|exact HatC]. cbn [fst snd hd_at]. rewrite H10'. exact H10. }
    unfold hs_at_cx. hvd_sub HatF. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Hm|]. split; [exact Hkey|].
  split; [exact Ht6|]. split; [exact Hpair|]. split; [exact Hcs|]. split; [exact Hx4|].
  split.
  { apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem4 _ 4 _); [|exact Vs].
    intros j Hj. change (Z.of_nat 4) with 4 in Hj. apply KB. lia. }
  split.
  { apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem4 _ 4 _); [|exact Vb].
    intros j Hj. change (Z.of_nat 4) with 4 in Hj. apply KB. lia. }
  apply (hm_ra_kept rsegs (w_H W2) mem2 (w_H W2) mem4 _ _ _ Hra). intros y Hy. apply KB.
  unfold shadow_of_addr, SHADOW_OFF.
  assert (Hd0 : 0 <= y / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : y / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  lia.
- (* RF: the type is none of Bool, Int, Float, or a Bool with a size below 4 *)
  apply (HRF fx2 ly2 S2 W2 regs4 mem4 md4 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
  split; [exact Hb4|].
  split; [unfold hs_at_cx; hvd_sub HatC|].
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Hm|].
  split.
  { apply (hvm_cell_inl k v ch p Hkey). left.
    destruct Hrf as [(Hn2 & Hn4 & Hn6) | (Ht2 & Hs4)].
    - rewrite (hvm_cv_other v Hvwf Hn2 Hn4 Hn6). lia.
    - rewrite (hvm_cv_small v Hvwf Hs4). lia. }
  split; [right; reflexivity|]. split; [exact Hpair | exact Hx4].
- (* RFA: an Int with a size below 4 or a value of 256 or more *)
  apply (HRFA fx2 ly2 S2 W2 regs4 mem4 md4 k v cs keys rf).
  split; [exact Hb4|].
  split; [unfold hs_at_cx; hvd_sub HatC|].
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Hm|].
  split.
  { apply (hvm_cell_inl k v ch p Hkey). left.
    destruct Hrfa as [Hs4 | (Hs4 & Hbig)].
    - rewrite (hvm_cv_small v Hvwf Hs4). lia.
    - rewrite (hvm_cv_int v Hvwf Ht4 Hs4), (proj2 (Z.leb_gt _ _) Hbig). lia. }
  split; [exact Hpair | exact Hx4].
- (* TAIL: an Int whose value is below 256 *)
  apply (HTAIL fx2 ly2 S2 W2 regs4 mem4 md4 k v ch p (Cursor.rd32 (Model.e_body v)) cs keys rf).
  split; [exact Hb4|].
  split.
  { assert (HatT : hs_at rsegs (w_H W2) mem4 regs4 (x_e rsegs cx)
      ((LReg 20, Cursor.rd32 (Model.e_body v)) :: (LCell XR 0x98, p) :: hvd_L cx r m ch p)).
    { apply Forall_cons; [exact H20|]. apply Forall_cons; [exact V98 | exact HatC]. }
    unfold hs_at_cx. hvd_sub HatT. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Hm|]. split; [exact Hkey|].
  split; [rewrite (hvm_cv_int v Hvwf Ht4 Hs4), (proj2 (Z.leb_le _ _) Hbw'); reflexivity|].
  split; [lia|]. split; [exact Hpair|]. split; [exact Hcs | exact Hx4].
- (* CELL: a Bool, its value 0 or 1 *)
  pose proof (hvm_cv_bool v Hvwf Ht2 Hs4) as Hcv.
  assert (Hv01 : 0 <= Headamp.cell_value v <= 1)
    by (rewrite Hcv; destruct (Cursor.rd32 (Model.e_body v) =? 0); lia).
  pose proof (hvm_top_bounds p) as Htop.
  apply (HCELL fx2 ly2 S2 W2 regs4 mem4 md4 k v ch p (Headamp.cell_value v) cs keys rf).
  split; [exact Hb4|].
  split.
  { assert (HatT : hs_at rsegs (w_H W2) mem4 regs4 (x_e rsegs cx)
      ((LReg 20, Headamp.cell_value v) :: (LCell XR 0x98, p) :: hvd_L cx r m ch p)).
    { apply Forall_cons; [cbn [fst snd hd_at]; rewrite Hcv; exact H20|].
      apply Forall_cons; [exact V98 | exact HatC]. }
    unfold hs_at_cx. hvd_sub HatT. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Hm|].
  split; [apply (hvm_cell_inr k v ch p Hkey); lia|].
  split; [apply hvm_valid; [exact Hch | exact Hp | lia]|].
  split; [exact Hpair|]. split; [exact Hcs | exact Hx4].
Qed.

End c.

Print Assumptions hvd_blk1.
Print Assumptions hvd_blk2.
Print Assumptions hvd_disp_A.
