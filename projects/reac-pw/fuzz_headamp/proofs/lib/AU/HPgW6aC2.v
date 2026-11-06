(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 80bf14ccf11; restated for
   reac-pw/fuzz_headamp image B against lib/AU/HPgW6aBase.v's w6b_c2_stmt: image B's registers (s1 = R, s11 = the
   shadow offset, s2 = the cursor, s4 = what is left, a7 = c - 1, t1 = what was left before the kind byte), image B's
   pcs and its real-frame cells [R+0x130] = &e62 and [R+0x148] = pp, the post lib/AU/HPgSteps.v's hdu_blk_postE with
   no byte written, the odd arm stopped at hdu_u32_block2's entry 0x82390, the index block split at 0x81cf4 with
   image B's UBSan pointer-overflow test 0x81d24 refuted by a bounded check, the no-byte arm joining the even arm's
   load at 0x820b0 (image B's join of the two even arms), the chaining from lib/AU/HPgCaseB.v's cb_post_seq. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the block lemma w6b_c2 of lib/AU/HPgW6aBase.v, the head of case 2 of ent_build's `switch (kind % 10)`
   (pod.h:298-303) inside LLVMFuzzerTestOneInput (0x80c40). Proves no function (kind: segment lemma).

   THE CODE (registers as HPgW6aBase.v names them: s1 = R, s11 = SHADOW_OFF, s2 = c the cursor, s4 = |r|, a7 = c - 1,
   t1 = |r| + 1, a6 = 1):
     0x81cbc  beqz s4 -> 0x820a0                    no byte left: m = 0
     0x81cc0 .. 0x81cc8  a0 := s2 + 1; `bltu a6,a0` (fuzz.h:42; its `unimp` arm 0x81cc8 needs c + 1 <=u 1, and c >= 2)
     0x81ccc .. 0x81cdc  the shadow check of s2 (NE-SLOW, slow block 0x827f8), with `ld s7,0x148(s1)` (= pp) inside
     0x81ce0  lbu a1,0(s2) (= m); a2 := t1 - 2; a3 := m & 1; s2 := a7 + 2
     0x81cf0  bnez a3 -> 0x8238c                    m odd: `ld s4,0x130(s1)` (= &e62), stop at 0x82390
     0x81cf4 .. 0x81d30  m even: a3 := 4 * ((m >> 1) % 14) (`ld` of the cell 0x10318, mulhu, shifts); a4 := ~&ints[0];
              `bgeu a4,a3` 0x81d24 (pod.h:300; its `unimp` arm 0x81d28 is dead: a3 <= 52); a1 := &ints[0] + a3; j 0x820b0
     0x820a0 .. 0x820ac  no byte: a2 := 0; a1 := &ints[0]; s7 := [R+0x148] (= pp)
     0x820b0 .. 0x820cc  the shadow check of a1 (NE-SLOW, slow block 0x827b4), s4 := [R+0x130], a4 := 4;
              lw a1,0(a1); j 0x82578
   THE PROOF is cut in blocks, each an entry state, the token engine's runs (lib/Reusable/YCbn.v, YCbq.v
   aj_run_to_tok, which follows each NE-SLOW slow block itself and leaves one obligation `range_addressable ...` per
   check) and its post:
     c2_ld_block   0x820b0 .. 0x82578: a1 is the register atom x11 and the int's 4 bytes a one-chunk region based at
                   it (their value the extra slot 32; a computed a1 would not show the engine the check's
                   `(x >> 3) + s11` form); the bytes come from the image (rom_view, c2_ints_ok); the check's
                   obligation from the statement's range_addressable of ints.
     c2_idx_block  0x81cf4 .. 0x820b0: the 8-byte cell 0x10318 as a base-free image region; the pointer-overflow test
                   split by srr_branch_tok (YCbm.v), its trap arm refuted and a1's value given by c2_ovf_ok /
                   c2_a1_val, each one bounded check over the 256 byte values (c2_all256).
     c2_int_block  the two chained by lib/AU/HPgCaseB.v's cb_post_seq.
     w6b_c2        0x81cbc .. 0x81cf4 / 0x82390 / 0x820b0: the two cells [R+0x130], [R+0x148] as a region based at
                   s1, the input byte as a one-byte region based at s2 whose value is the extra slot 34; the branch
                   on m & 1 split by srr_branch_tok (c2_parity); the even arm chained with c2_int_block and the
                   no-byte arm with c2_ld_block by c2_chain. The block writes no byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YP08 YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgCaseB HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the blocks' states ======================================== *)
Definition C2_IDX : Z := 0x81cf4.    (* m even: the index (m >> 1) % 14 and &ints[.] *)
Definition C2_PIN : Z := 0x820b0.    (* a1 = &ints[.]: its check and the `lw` *)
Definition C2_K14 : Z := 0x10318.    (* the 8-byte constant ceil(2 ^ 64 / 14) *)
(* the shadow base is s11's own atom, pinned to SHADOW_OFF by a fact *)
Definition c2_Bx : sv := SOff 27 0.
Definition c2_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition c2_shf : nat * afact := (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
(* the case's entry: [R+0x130] = &e62 (slot 32), [R+0x148] = pp (slot 33); with a byte left, m at c (slot 34) *)
Definition c2_s1_region : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x150 0 0
  [YP09.mkChunk 0x130 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x148 (CVal 8 (SOff 33 0))].
Definition c2_in_region : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition c2_facts1 : facts :=
  mkFacts [(16%nat, mkAF 1 1 0); (18%nat, mkAF 2 (2 ^ 47 - 2) 0); (20%nat, mkAF 1 (2 ^ 47) 0); c2_shf;
           (34%nat, mkAF 0 255 0)] [] [].
Definition c2_ss1 : sstate := mkSS W6B_D2 sr_atoms [c2_s1_region; c2_in_region] None c2_facts1.
Definition c2_extra1 (e p m : Z) : list word := [w64 e; w64 p; w64 m].
Definition c2_facts0 : facts := mkFacts [c2_shf] [] [].
Definition c2_ss0 : sstate := mkSS W6B_D2 sr_atoms [c2_s1_region] None c2_facts0.
Definition c2_extra0 (e p : Z) : list word := [w64 e; w64 p].
(* the index block: the constant as a base-free image region, m in a1 (atom 11) *)
Definition c2_k14_region : YP09.region := YP09.mkRegion None C2_K14 (C2_K14 + 8) 0 0 [YP09.mkChunk C2_K14 (CImg 8)].
Definition c2_factsi : facts := mkFacts [(11%nat, mkAF 0 255 0)] [] [].
Definition c2_ssi : sstate := mkSS C2_IDX sr_atoms [c2_k14_region] None c2_factsi.
(* the load block: a1 = &ints[i], its 4 bytes the value of slot 32; [R+0x130] = &e62 (slot 33) *)
Definition c2_ld_region : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition c2_e_region : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0 [YP09.mkChunk 0x130 (CVal 8 (SOff 33 0))].
Definition c2_factsl : facts := mkFacts [c2_shf; (11%nat, mkAF W6B_INTS (W6B_INTS + 52) 2)] [] [].
Definition c2_ssl : sstate := mkSS C2_PIN sr_atoms [c2_ld_region; c2_e_region] None c2_factsl.
(* ints[i] as its 4 bytes hold it *)
Definition c2_int32 (i : Z) : Z := nth (Z.to_nat i) Tables.ints 0 mod 2 ^ 32.

(* ======================================== the arithmetic ======================================== *)
(* a3 at 0x81d24 as the engine forms it from a1 = m (atom 11): 4 * ((m >> 1) - 14 * mulhu (m >> 1, ceil(2^64/14))) *)
Definition c2_hm : sv := SAlu ALU_SRL (SOff 11 0) (SLit 1).
Definition c2_q : sv := SMd M_MULHU c2_hm (SLit 0x124924924924924a).
Definition c2_ix : sv :=
  SAlu ALU_SLL (SAlu ALU_ADD c2_hm (SAlu ALU_SUB (SAlu ALU_SLL c2_q (SLit 1)) (SAlu ALU_SLL c2_q (SLit 4)))) (SLit 2).
(* the remainder: mulhu by the cell 0x10318 is the quotient by 14 on 0 .. 127, and the four instructions after it
   leave 4 * ((m >> 1) % 14); one bounded check over the 256 byte values *)
Lemma c2_ix_val : forall E m, ew E 11 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c2_ix = Z_to_bv 64 (4 * ((m / 2) mod 14)).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (cb_envz m) c2_ix); [unfold c2_ix, c2_q, c2_hm; cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (cb_all256 (fun m => bv_unsigned (sv_denot (cb_envz m) c2_ix) =? bv_unsigned (Z_to_bv 64 (4 * ((m / 2) mod 14))))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
(* the address a1 = &ints[0] + a3 at 0x820b0 *)
Lemma c2_a1_val : forall E m, ew E 11 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E (SAlu ALU_ADD (SLit W6B_INTS) c2_ix) = Z_to_bv 64 (W6B_INTS + 4 * ((m / 2) mod 14)).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (cb_envz m) (SAlu ALU_ADD (SLit W6B_INTS) c2_ix));
  [unfold c2_ix, c2_q, c2_hm; cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (cb_all256 (fun m => bv_unsigned (sv_denot (cb_envz m) (SAlu ALU_ADD (SLit W6B_INTS) c2_ix)) =?
  bv_unsigned (Z_to_bv 64 (W6B_INTS + 4 * ((m / 2) mod 14)))) ltac:(vm_compute; reflexivity) m Hr).
Qed.
(* the UBSan pointer-overflow test `bgeu a4,a3` 0x81d24 (a4 = ~&ints[0]) holds: a3 is at most 52 *)
Lemma c2_ovf_ok : forall E m, ew E 11 = Z_to_bv 64 m -> 0 <= m < 256 ->
  branch_taken BC_GEU (sv_denot E (SLit 18446744073709416383)) (sv_denot E c2_ix) = true.
Proof.
intros E m Hm Hr.
transitivity (branch_taken BC_GEU (sv_denot (cb_envz m) (SLit 18446744073709416383)) (sv_denot (cb_envz m) c2_ix));
  [unfold c2_ix, c2_q, c2_hm; cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
exact (cb_all256 (fun m => branch_taken BC_GEU (sv_denot (cb_envz m) (SLit 18446744073709416383)) (sv_denot (cb_envz m) c2_ix))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
(* `bnez a3` with a3 = m & 1 is taken exactly when m is odd *)
Lemma c2_parity : forall E m, ew E 34 = Z_to_bv 64 m -> 0 <= m < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 1))) (sv_denot E (SLit 0)) = Z.odd m.
Proof.
intros E m Hm Hr.
transitivity (branch_taken BC_NE (sv_denot (cb_envz m) (SAlu ALU_AND (SOff 34 0) (SLit 1))) (sv_denot (cb_envz m) (SLit 0)));
  [cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
apply Bool.eqb_prop.
exact (cb_all256 (fun m => Bool.eqb (branch_taken BC_NE (sv_denot (cb_envz m) (SAlu ALU_AND (SOff 34 0) (SLit 1)))
  (sv_denot (cb_envz m) (SLit 0))) (Z.odd m)) ltac:(vm_compute; reflexivity) m Hr).
Qed.
(* `lw` sign-extends; the low 4 bytes are the value *)
Lemma c2_sext_low : forall v, 0 <= v < 2 ^ 32 -> bv_unsigned (sext 64 (bv_extract 0 32 (Z_to_bv 64 v))) mod 2 ^ 32 = v.
Proof.
intros v Hv. change (2 ^ 32) with (2 ^ Z.of_N 32) at 1.
rewrite <- extract_unsigned_mod. change (bv_extract 0 32 (sext 64 (bv_extract 0 32 (Z_to_bv 64 v))))
  with (low32 (sext 64 (bv_extract 0 32 (Z_to_bv 64 v)))).
rewrite low32_sext32, extract_unsigned_mod, unsigned_lit_small by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_small. exact Hv.
Qed.

(* ======================================== the image's bytes ======================================== *)
(* ints[0 .. 14) at 0x21040: read-only bytes of image B, 4 little-endian bytes each *)
Definition c2_ints_ok : bool :=
  forallb (fun i => forallb (fun k =>
    in_rom_b (W6B_INTS + 4 * Z.of_nat i + Z.of_nat k) && YP08.img_byte_ok rsegs (W6B_INTS + 4 * Z.of_nat i + Z.of_nat k) &&
    match img_byte rsegs (W6B_INTS + 4 * Z.of_nat i + Z.of_nat k) with
    | Some b => bv_unsigned b =? YO0f.le_byte (c2_int32 (Z.of_nat i)) 4 k
    | None => false
    end) (seq 0 4)) (seq 0 14).
Lemma c2_ints_ok_true : c2_ints_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c2_ints_val : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (W : world rsegs) mem i,
  rom_view rsegs W mem -> 0 <= i < 14 ->
  val_mem rsegs (mrestrict (w_H W) mem) (W6B_INTS + 4 * i) 4 (c2_int32 i).
Proof.
intros fx rc W mem i HR Hi k Hk.
pose proof (proj1 (forallb_forall _ _) c2_ints_ok_true (Z.to_nat i) ltac:(apply in_seq; lia)) as H1.
pose proof (proj1 (forallb_forall _ _) H1 k ltac:(apply in_seq; lia)) as H2. cbv beta in H2.
rewrite Z2Nat.id in H2 by lia.
apply andb_prop in H2 as [H2 H4]. apply andb_prop in H2 as [H2 H3].
destruct (mbyte_rom W mem _ HR H2 H3) as (b & Hb & Hm).
rewrite Hm. rewrite Hb in H4. apply Z.eqb_eq in H4. rewrite <- H4. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ======================================== small helpers ======================================== *)
Lemma c2_af : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia. auto. Qed.
Section av. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a byte view equal on [0, 2 ^ 64) is equal everywhere (mbyte reads at the address mod 2 ^ 64) *)
Lemma c2_av_full : forall (H H' : word -> bool) m m',
  (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs H' m' a = aview rsegs H m a) ->
  forall a, aview rsegs H' m' a = aview rsegs H m a.
Proof.
intros H H' m m' Hk a. pose proof (Hk (a mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia) (fun x => x)) as E.
unfold aview, mbyte in *. rewrite !Z_to_bv_mod64 in E. exact E.
Qed.
Lemma c2_rom_eq : forall (W W' : world rsegs) m m', (forall a, aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a) ->
  rom_view rsegs W m -> rom_view rsegs W' m'.
Proof. intros W W' m m' He HR a Ha. rewrite He. exact (HR a Ha). Qed.
Lemma c2_ra_eq : forall (rd rd' : reader) Bs a n, (forall x, rd' x = rd x) ->
  range_addressable rd Bs a n -> range_addressable rd' Bs a n.
Proof. intros rd rd' Bs a n He H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite He. auto. Qed.
Lemma c2_vm_eq : forall (W W' : world rsegs) m m' a n v, (forall x, aview rsegs (w_H W') m' x = aview rsegs (w_H W) m x) ->
  val_mem rsegs (mrestrict (w_H W) m) a n v -> val_mem rsegs (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v He H k Hk. pose proof (He (a + Z.of_nat k)) as E. specialize (H k Hk).
unfold aview in E. rewrite H in E. cbn [option_map] in E.
destruct (mbyte rsegs (mrestrict (w_H W') m') (a + Z.of_nat k)) as [b|]; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
End av.
(* a run whose regions have no write window keeps every byte *)
Lemma c2_keep_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
  (forall a, aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 K HF Hro a. rewrite <- (K a). unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
Ltac c2_keep :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, aview _ _ _ a = _ |- _ =>
    let KS := fresh "KS" in
    pose proof (c2_keep_step _ _ _ _ _ _ KE HFr ltac:(vm_compute; reflexivity)) as KS;
    clear KE HFr; rename KS into KE
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ => clear old end.
(* a register of the state after a run, as its symbolic value's denotation *)
Ltac c2_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia
  end.
(* the state a run stopped in, as a cfg_at at its pc *)
Ltac c2_at pc :=
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs _ _ _ ms HS eq_refl) end;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 pc) mm (seg_rom rsegs)) md) with (cfg_at rsegs pc rg mm md) end.
Ltac c2_kept := first [apply cb_nz; reflexivity | apply cb_notin; reflexivity].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* the leaf of a run into a block post that writes nothing: everything but R *)
Ltac c2_leaf HAE Rtac :=
  apply SRr_ret;
  lazymatch goal with
  | HS : st_ok _ _ _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
    KE : forall a, aview _ _ _ a = _ |- _ =>
    red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
    split; [exact HJ|];
    split; [eapply (regs_kept_of_st_ok rsegs _ _ ms _ _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity]|];
    split; [reflexivity|];
    split; [apply Permutation_refl|];
    split; [cb_kio|];
    split; [apply mo_le_refl; exact MTL|];
    split; [intros a _ _; exact (KE a) | cbv beta; Rtac]
  end.

(* a block that starts where a run stopped, re-stated over the run's own start *)
Lemma c2_chain : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc regs1 mem1 md1 pc1 pc2
  (clob1 clob2 clob : list (bv 5)) (Wr2 Wr : Z -> Prop)
  (R2 R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
  same_io mdc md1 ->
  (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
  incl clob1 clob -> incl clob2 clob -> (forall a, Wr2 a -> Wr a) ->
  (forall W2 regs2 mem2, R2 W2 regs2 mem2 ->
    (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob2 -> getr regs2 r = getr regs1 r) -> R W2 regs2 mem2) ->
  SRr rsegs W (cfg_at rsegs pc1 regs1 mem1 md1)
    (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 lyc Sc W mem1 md1 pc2 clob2 Wr2 R2) ->
  SRr rsegs W (cfg_at rsegs pc1 regs1 mem1 md1)
    (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 clob Wr R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc regs1 mem1 md1 pc1 pc2 clob1 clob2 clob Wr2 Wr R2 R
  Hr1 Hio1 Hm1 Hi1 Hi2 HWr HRR H.
eapply SRr_mono; [exact H|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply Hi2; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply Hi1; exact X]|].
split; [exact Hf2|]. split; [exact Hp2|]. split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact Hmo2|]. split; [intros a Ha Hn; rewrite (Hm2 a Ha (fun X => Hn (HWr a X))); apply Hm1|].
exact (HRR W2 regs2 mem2 HR2 Hr2).
Qed.
(* ---- 0x820b0 .. 0x82578: the check of ints[i], s4 := [R+0x130], a4 := 4, the `lw` ---- *)
Lemma c2_ld_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R e i,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_INTS 56 ->
  getr regs 11 = w64 (W6B_INTS + 4 * i) -> 0 <= i < 14 -> getr regs 27 = w64 SHADOW_OFF ->
  getr regs 9 = w64 R -> W6B_INTS + 56 <= R -> R + 0x138 <= 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 e -> 0 <= e < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs C2_PIN regs memc mdc)
  (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_T2 [10; 11; 13; 14; 20]%bv (fun _ => False)
    (fun _ regs2 _ => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat i) Tables.ints 0 mod 2 ^ 32) /\
       getr regs2 14 = w64 4 /\ getr regs2 20 = w64 e)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R e i HJ HR Hra H11 Hi H27 H9 HR0 HR1 Hve He.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof LAWS as HLAWS.
set (ex := [w64 (c2_int32 i); w64 e]).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 (W6B_INTS + 4 * i))
  by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (c2_int32 i)) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 e) by exact (ew_Ereg_extra regs _ 1).
assert (Hv : 0 <= c2_int32 i < 2 ^ 32) by (unfold c2_int32; apply Z.mod_pos_bound; lia).
assert (HS : st_ok rsegs (Ereg regs ex) c2_ssl
  (restrict (w_H W) (mkst regs (Z_to_bv 64 C2_PIN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, c2_ld_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E11, unsigned_lit_small by (unfold W6B_INTS; lia).
      split; [unfold W6B_INTS; lia|]. split; [unfold W6B_INTS; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 32 0) (c2_int32 i)).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
      * cbn. lia.
      * rewrite Z.add_0_r. exact (c2_ints_val W memc i HR Hi).
    + unfold region_ok, c2_e_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by (unfold W6B_INTS in *; lia).
      split; [unfold W6B_INTS in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0x130 8 (SOff 33 0) e).
      * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact He.
      * cbn. lia.
      * exact Hve.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c2_ld_region, c2_e_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E11, E9, !unsigned_lit_small by (unfold W6B_INTS in *; lia).
    unfold W6B_INTS in *. split; [split; [lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [c2_factsl c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c2_af _ _ _ _ _ _ E27); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
    + apply (c2_af _ _ _ _ _ _ E11); unfold W6B_INTS; [lia | lia | | lia].
      rewrite (Z.mul_comm 4 i). change (2 ^ 2) with 4. rewrite Z.mod_add by lia. reflexivity. }
assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C2_PIN) with (Z_to_bv 64 C2_PIN).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan W6B_T2.
- apply (obl_of_range rsegs (w_H W) memc _ c2_Bx _ _ W6B_INTS 56 Hra).
  + apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
  + rewrite (U_atom _ 11 (W6B_INTS + 4 * i) E11) by (unfold W6B_INTS; lia). lia.
  + rewrite (U_atom _ 11 (W6B_INTS + 4 * i) E11) by (unfold W6B_INTS; lia). lia.
- awr_ok_tac.
- c2_keep.
  c2_leaf HAE idtac.
  split; [|split].
  + lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      exists (bv_unsigned (getr (ms_regs ms) 11)); split; [unfold w64; symmetry; apply Z_to_bv_bv_unsigned|] end.
    c2_regv HS (11%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite c2_sext_low by exact Hv. reflexivity.
  + c2_regv HS (14%bv : bv 5). reflexivity.
  + c2_regv HS (20%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- 0x81cf4 .. 0x820b0: the index (m >> 1) % 14, the pointer-overflow test, a1 := &ints[.] ---- *)
Lemma c2_idx_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  getr regs 11 = w64 m -> 0 <= m < 256 ->
  SRr rsegs W (cfg_at rsegs C2_IDX regs memc mdc)
  (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C2_PIN [11; 13; 14]%bv
    (fun _ => False) (fun _ regs2 _ => getr regs2 11 = w64 (W6B_INTS + 4 * ((m / 2) mod 14)))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR H11 Hm.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof LAWS as HLAWS.
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 m) by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HS : st_ok rsegs (Ereg regs []) c2_ssi (restrict (w_H W) (mkst regs (Z_to_bv 64 C2_IDX) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply img_region_ok_rom; [exact HR | unfold C2_K14; lia | unfold C2_K14; lia | lia | vm_compute; reflexivity].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [c2_factsi f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    apply (c2_af _ _ _ _ _ _ E11); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C2_IDX) with (Z_to_bv 64 C2_IDX).
(* 0x81cf4 .. the test `bgeu a4,a3` 0x81d24 *)
aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_PIN.
{ awr_ok_tac. }
c2_keep.
srr_branch_tok w6b_tbl_ok HS SHOK c2_Bspan.
- (* the test holds: 0x81d2c a1 := &ints[0] + a3, j 0x820b0 *)
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_PIN; [awr_ok_tac|].
  c2_keep.
  c2_leaf HAE idtac.
  lazymatch goal with HS : st_ok _ _ ?ssf (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 11%bv HS);
    replace (sr_get (ss_regs ssf) (11%bv : bv 5)) with (SAlu ALU_ADD (SLit W6B_INTS) c2_ix) by (vm_compute; reflexivity) end.
  exact (c2_a1_val _ m E11 Hm).
- (* the trap arm 0x81d28 is dead: the index is at most 13 *)
  exfalso. pose proof (c2_ovf_ok (Ereg regs []) m E11 Hm) as Ho. unfold c2_ix, c2_q, c2_hm in Ho.
  rewrite Ho in Hc. discriminate Hc.
Qed.

(* ---- 0x81cf4 .. 0x82578: ints[(m >> 1) % 14] ---- *)
Lemma c2_int_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R e m,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_INTS 56 ->
  getr regs 11 = w64 m -> 0 <= m < 256 -> getr regs 27 = w64 SHADOW_OFF ->
  getr regs 9 = w64 R -> W6B_INTS + 56 <= R -> R + 0x138 <= 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 e -> 0 <= e < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs C2_IDX regs memc mdc)
  (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_T2 ([11; 13; 14] ++ [10; 11; 13; 14; 20])%bv
    (fun _ => False \/ False)
    (fun _ regs2 _ => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = w6b_int_even m mod 2 ^ 32) /\
       getr regs2 14 = w64 4 /\ getr regs2 20 = w64 e)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R e m HJ HR Hra H11 Hm H27 H9 HRlo HRhi Hve He.
refine (cb_post_seq B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C2_IDX C2_PIN W6B_T2 _ _
  (fun _ => False) (fun _ => False) (fun _ regs2 _ => getr regs2 11 = w64 (W6B_INTS + 4 * ((m / 2) mod 14))) _ _ _).
- exact (c2_idx_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR H11 Hm).
- intros W1 ly1 S1 regs1 mem1 md1 Hw HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1r HR1.
  pose proof (c2_av_full _ _ _ _ Hm1r) as Hm1.
  apply (c2_ld_block STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R e ((m / 2) mod 14) HJ1).
  + exact (c2_rom_eq W W1 memc mem1 Hm1 HR).
  + exact (c2_ra_eq _ _ _ _ _ Hm1 Hra).
  + exact HR1.
  + apply Z.mod_pos_bound. lia.
  + rewrite Hr1; [exact H27 | c2_kept | c2_kept].
  + rewrite Hr1; [exact H9 | c2_kept | c2_kept].
  + exact HRlo.
  + exact HRhi.
  + exact (c2_vm_eq W W1 memc mem1 _ _ _ Hm1 Hve).
  + exact He.
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem w6b_c2 : w6b_c2_stmt B MT.
Proof using MTL.
unfold w6b_c2_stmt, w6b_case_stmt. cbv beta iota.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pp c r Hctx Hin Hra.
destruct Hctx as (HJ & HR32 & HRsp & HspR & Hown & HFa & HR).
destruct Hin as (H2 & H9 & H27 & H17 & H18 & H6 & H20 & H16 & Hve & Hvp & Hc1 & Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof ASAN_CEIL_range as [Hac _]. unfold ASAN_CEIL in Hac.
unfold T_SEG_STK, ASTACK in HspR, Hdis.
assert (HRb : 0x7fff7f804000 <= R /\ R + 0x220 <= 2 ^ 47) by lia.
clear Hsp0al Hceil Hslo Hshi H47 Hac.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof LAWS as HLAWS.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
set (e := (F + 0x210) mod 2 ^ 64).
set (p := pp mod 2 ^ 64).
assert (He : 0 <= e < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (Hp : 0 <= p < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (Hwe : w64 (F + 0x210) = Z_to_bv 64 e) by (unfold w64, e; symmetry; apply Z_to_bv_mod64).
assert (Hwp : w64 pp = Z_to_bv 64 p) by (unfold w64, p; symmetry; apply Z_to_bv_mod64).
pose proof (proj2 (cb_val_mod _ _ _) Hve) as Hve'. fold e in Hve'. clear Hve.
pose proof (proj2 (cb_val_mod _ _ _) Hvp) as Hvp'. fold p in Hvp'. clear Hvp.
unfold w6b_case_odd_R, w6b_case_even_R, w6b_even_val.
destruct r as [|b r'].
- (* no byte left: m = 0, ints[0] *)
  cbn [Cursor.fuzz_u8 fst snd Z.odd length Nat.sub Z.of_nat] in *.
  set (ex := c2_extra0 e p).
  assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E20 : ew (Ereg regs ex) 20 = Z_to_bv 64 0) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 e) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 p) by exact (ew_Ereg_extra regs _ 1).
  assert (HS : st_ok rsegs (Ereg regs ex) c2_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D2) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok, c2_s1_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
      + apply (chunk_ok_val rsegs _ _ _ 0x130 8 (SOff 32 0) e);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hve'].
      + apply (chunk_ok_val rsegs _ _ _ 0x148 8 (SOff 33 0) p);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvp'].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [c2_facts0 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|exact I].
      apply (c2_af _ _ _ _ _ _ E27); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
  (* s4 = 0: pinned to the literal, for `beqz s4` *)
  pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; exact H20)) as HS1.
  clear HS. rename HS1 into HS.
  assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D2) with (Z_to_bv 64 W6B_D2).
  (* 0x81cbc `beqz s4` -> 0x820a0: a2 := 0, a1 := &ints[0], s7 := pp; to 0x820b0 *)
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_PIN; [awr_ok_tac|].
  c2_keep.
  c2_at C2_PIN.
  eapply (c2_chain STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ _ _ C2_PIN W6B_T2
    [10; 11; 12; 20; 23]%bv [10; 11; 13; 14; 20]%bv w6b_case_clob (fun _ => False) (fun _ => False)
    (fun _ regs2 _ => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat 0) Tables.ints 0 mod 2 ^ 32) /\
       getr regs2 14 = w64 4 /\ getr regs2 20 = w64 e) _).
  + eapply (regs_kept_of_st_ok rsegs _ _ _ regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + cb_kio.
  + exact KE.
  + intros x Hx. cbv [w6b_case_clob In] in Hx |- *. tauto.
  + intros x Hx. cbv [w6b_case_clob In] in Hx |- *. tauto.
  + intros a Ha. exact Ha.
  + intros W2 regs2 mem2 ((v & Hv & Hvm) & H14 & H20') Hk2.
    split; [exists v; split; [exact Hv | unfold w6b_int_even; exact Hvm]|].
    rewrite (Hk2 12%bv), (Hk2 18%bv), (Hk2 23%bv) by c2_kept.
    split; [c2_regv HS (12%bv : bv 5); reflexivity|].
    split; [exact H14|].
    split; [c2_regv HS (18%bv : bv 5); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite H20', Hwe; reflexivity|].
    c2_regv HS (23%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. exact (eq_sym Hwp).
  + apply (c2_ld_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k _ R e 0 HJ).
    * exact (c2_rom_eq W W memc _ KE HR).
    * exact (c2_ra_eq _ _ _ _ _ KE Hra).
    * c2_regv HS (11%bv : bv 5). reflexivity.
    * lia.
    * c2_regv HS (27%bv : bv 5). rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * c2_regv HS (9%bv : bv 5). rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * unfold W6B_INTS. lia.
    * lia.
    * exact (c2_vm_eq W W memc _ _ _ _ KE Hve').
    * exact He.
- (* a byte m = b, the rest r' *)
  cbn [Cursor.fuzz_u8 fst snd].
  pose proof (Cursor.byte_range b) as Hmb.
  set (m := bv_unsigned b) in *.
  set (n := Z.of_nat (length (b :: r'))) in *.
  assert (Hn : n = Z.of_nat (length r') + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : c < R - 16384 \/ R + 0x198 <= c).
  { pose proof (Hdis c ltac:(lia)) as Hd. lia. }
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  set (ex := c2_extra1 e p m).
  assert (E6 : ew (Ereg regs ex) 6 = Z_to_bv 64 (n + 1)) by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 1) by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
  assert (E17 : ew (Ereg regs ex) 17 = Z_to_bv 64 (c - 1)) by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew (Ereg regs ex) 20 = Z_to_bv 64 n) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 e) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 p) by exact (ew_Ereg_extra regs _ 1).
  assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 m) by exact (ew_Ereg_extra regs _ 2).
  assert (HS : st_ok rsegs (Ereg regs ex) c2_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D2) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok, c2_s1_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val rsegs _ _ _ 0x130 8 (SOff 32 0) e);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hve'].
        * apply (chunk_ok_val rsegs _ _ _ 0x148 8 (SOff 33 0) p);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvp'].
      + unfold region_ok, c2_in_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E18, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 34 0) m);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm0].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c2_s1_region, c2_in_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E18, !unsigned_lit_small by lia.
      split; [split; [lia | exact I] | split; exact I].
    - unfold facts_ok. cbn [c2_facts1 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
      + apply (c2_af _ _ _ _ _ _ E16); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E18); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E20); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E27); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E34); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D2) with (Z_to_bv 64 W6B_D2).
  (* 0x81cbc .. the branch on m & 1 at 0x81cf0 *)
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_IDX.
  { apply (obl_of_range rsegs (w_H W) memc _ c2_Bx _ _ c n Hrain).
    - apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia. }
  { awr_ok_tac. }
  c2_keep.
  srr_branch_tok w6b_tbl_ok HS SHOK c2_Bspan.
  + (* m odd: 0x8238c s4 := [R+0x130], stop at 0x82390 *)
    rewrite (c2_parity _ m) in Hc; [| rewrite ?ew_ewset_other by lia; exact E34 | exact Hmb].
    rewrite Hc. cbv beta iota.
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan W6B_U2; [awr_ok_tac|].
    c2_keep.
    c2_leaf HAE idtac.
    split; [c2_regv HS (12%bv : bv 5); rewrite E6, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [c2_regv HS (18%bv : bv 5); rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [c2_regv HS (20%bv : bv 5); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym Hwe)|].
    c2_regv HS (23%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. exact (eq_sym Hwp).
  + (* m even: to 0x81cf4, then the int *)
    rewrite (c2_parity _ m) in Hc; [| rewrite ?ew_ewset_other by lia; exact E34 | exact Hmb].
    rewrite Hc. cbv beta iota.
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_IDX; [awr_ok_tac|].
    c2_keep.
    c2_at C2_IDX.
    eapply (c2_chain STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ _ _ C2_IDX W6B_T2
      [10; 11; 12; 13; 18; 23]%bv ([11; 13; 14] ++ [10; 11; 13; 14; 20])%bv w6b_case_clob
      (fun _ => False \/ False) (fun _ => False)
      (fun _ regs2 _ => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = w6b_int_even m mod 2 ^ 32) /\
         getr regs2 14 = w64 4 /\ getr regs2 20 = w64 e) _).
    * eapply (regs_kept_of_st_ok rsegs _ _ _ regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
    * cb_kio.
    * exact KE.
    * intros x Hx. cbv [w6b_case_clob In] in Hx |- *. tauto.
    * intros x Hx. cbv [w6b_case_clob In app] in Hx |- *. tauto.
    * intros a [Ha|Ha]; exact Ha.
    * intros W2 regs2 mem2 ((v & Hv & Hvm) & H14 & H20') Hk2.
      split; [exists v; split; [exact Hv | exact Hvm]|].
      rewrite (Hk2 12%bv), (Hk2 18%bv), (Hk2 23%bv) by c2_kept.
      split; [c2_regv HS (12%bv : bv 5); rewrite E6, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
      split; [exact H14|].
      split; [c2_regv HS (18%bv : bv 5); rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; cbn [length]; lia|].
      split; [rewrite H20', Hwe; reflexivity|].
      c2_regv HS (23%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. exact (eq_sym Hwp).
    * apply (c2_int_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k _ R e m HJ).
      -- exact (c2_rom_eq W W memc _ KE HR).
      -- exact (c2_ra_eq _ _ _ _ _ KE Hra).
      -- c2_regv HS (11%bv : bv 5). rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- exact Hmb.
      -- c2_regv HS (27%bv : bv 5). rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- c2_regv HS (9%bv : bv 5). rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- unfold W6B_INTS. lia.
      -- lia.
      -- exact (c2_vm_eq W W memc _ _ _ _ KE Hve').
      -- exact He.
Qed.

End d.
End b.

Print Assumptions w6b_c2.
