(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): parse_items' other three CALL STEPS, for the parse_items walk
   (a Theorem Labs lane composes them), in the caller-generic shape of FSW_parse_items_grow.pig_call:
     pic_call_ps_84c4c : parse_string 0x84c4c -> 0x84c50 (the key; callee parse_string_spec, S0's parse_string_proof);
     pic_call_ms_84d78 : __asan_memset 0x84d78 -> 0x84d7c (the kid zeroed; runtime callee aintrin_realizesU OSet
                         PC_memset, FsRt's fr_memset);
     pic_call_pv_84d98 : parse_value 0x84d98 -> 0x84d9c at level k + 1 (callee parse_value_spec (S k)).
   Each goes from the call configuration to a continuation over the RESUME configuration at ra, stated in FSW_ret's
   fss_retT ra 144 cs rs gf under Ereg regs' (fs_extraT ++ xs), cs the caller's frame chunks (parametric), xs
   a Theorem Labs lane's numbering (07:45Z): xatom 0 / 1 / 2 = in->p / in->end / in->depth AT THE RESUME (in->p is the
   callee's new cursor after parse_string / parse_value), 3..15 = xr (the entry ra and s0..s11), 16..19 = kids' /
   keys' / n / cap' (grow's post), and after parse_string 20 / 21 = the key pointer a / its length klen.
   rs = pic_rs cap' (q region at atom 8, v region at atom 20, the kids block at xatom 16, the keys block at xatom 17),
   and after parse_string pic_rs_ps cap' klen (the key block at xatom 20 appended); gf = pic_gf / pic_gf_ps.
   The caller's journal runs at the RAISED window top ot with footprint [(v, v + 56)] ++ FS_PSTAT_FP and own generic.
   parse_string's and parse_value's journals run at the same top ot (rd_win); their footprints sit inside the caller's
   through FSW_K3.fsw_fp_sub (the statics: image bytes; the kid: a byte of the kids block, a TEMPORARY block of the
   caller, premise "tmp"). __asan_memset is a runtime callee: FSW_K.fsw_intrin_atU puts the caller's journal back.
   pic_resumeT is FSW_rres.fsw_resume_after_rtU_args_chunks with the frame [sf - f, sf) anywhere below the window top
   ot, its chunks read on any memory that agrees on the frame (the call memory through the callee's wkeep, or the
   runtime callee's frame clause). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_rres FSPstat FSH_Fn_reader
FSW_rd FSW_pj FSW_K3 FSW_parse_items_grow.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_parse_string FSW_pj_parse.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSW_grow_holds FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct PjIn WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar PjTree PjRoundTrip.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the resume shape (a Theorem Labs lane's numbering, 07:45Z) ================= *)
Definition pic_blk_region (a : nat) (len : Z) : YP09.region := YP09.mkRegion (Some a) 0 len 0 len [].
Definition pic_rs (cap' : Z) : list YP09.region :=
  [pig_q_region; pig_v_region; pic_blk_region (xatom 16) (56 * cap'); pic_blk_region (xatom 17) (8 * cap')].
Definition pic_rs_ps (cap' klen : Z) : list YP09.region := pic_rs cap' ++ [pic_blk_region (xatom 20) (klen + 1)].
Definition pic_gf : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (20%nat, mkAF 4096 (2 ^ 47 - 56) 3);
   (xatom 0, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 1, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 2, mkAF 0 3 0);
   (xatom 16, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4); (xatom 17, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4);
   (xatom 18, mkAF 0 (2 ^ 54) 0); (xatom 19, mkAF 0 (2 ^ 54) 0)].
Definition pic_gf_ps : list (nat * afact) :=
  pic_gf ++ [(xatom 20, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 21, mkAF 0 (2 ^ 54) 0)].
Definition pic_xs_ps (p e d : Z) (xr : list word) (k' y' n cap' a klen : Z) : list word :=
  pig_xs p e d xr k' y' n cap' ++ [Z_to_bv 64 a; Z_to_bv 64 klen].

(* a fact kept out of lia's sight (lia case-splits every disjunction in the context) *)
Definition pghide (P : Prop) : Prop := P.
Ltac pic_pd := first [ lia | match goal with H : pghide (_ \/ _) |- _ =>
  let H' := fresh in pose proof H as H'; unfold pghide in H'; destruct H'; solve [lia] end ].

Lemma pic_xs_ps_nth : forall p e d xr k' y' n cap' a klen, length xr = 13%nat ->
  (forall j, (j < 20)%nat -> nth j (pic_xs_ps p e d xr k' y' n cap' a klen) (Z_to_bv 64 0) =
                             nth j (pig_xs p e d xr k' y' n cap') (Z_to_bv 64 0)) /\
  nth 20 (pic_xs_ps p e d xr k' y' n cap' a klen) (Z_to_bv 64 0) = Z_to_bv 64 a /\
  nth 21 (pic_xs_ps p e d xr k' y' n cap' a klen) (Z_to_bv 64 0) = Z_to_bv 64 klen.
Proof.
intros p e d xr k' y' n cap' a klen Hl.
assert (L : length (pig_xs p e d xr k' y' n cap') = 20%nat)
  by (unfold pig_xs; rewrite !length_app, Hl; reflexivity).
unfold pic_xs_ps. split; [intros j Hj; apply app_nth1; lia|].
rewrite !app_nth2 by lia. rewrite L. split; reflexivity.
Qed.

Lemma pic_blk_wf : forall a len, 0 <= len -> YP09.region_wf (pic_blk_region a len) = true.
Proof.
intros a len H. unfold pic_blk_region, YP09.region_wf.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
apply andb_true_intro; split; [apply andb_true_intro; split | reflexivity].
- apply Z.leb_le; lia.
- apply orb_true_intro; right; apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.
Lemma pic_wf : forall cs cap', 0 <= cap' -> regions_wf [fstk_ret 144 cs] = true ->
  regions_wf (fsT_ret_regions 144 cs (pic_rs cap')) = true.
Proof.
intros cs cap' Hc H. unfold fsT_ret_regions, pic_rs. cbn [app regions_wf] in *. rewrite andb_true_r in H. rewrite H.
rewrite (pic_blk_wf (xatom 16) (56 * cap')), (pic_blk_wf (xatom 17) (8 * cap')) by lia.
vm_compute. reflexivity.
Qed.
Lemma pic_wf_ps : forall cs cap' klen, 0 <= cap' -> 0 <= klen -> regions_wf [fstk_ret 144 cs] = true ->
  regions_wf (fsT_ret_regions 144 cs (pic_rs_ps cap' klen)) = true.
Proof.
intros cs cap' klen Hc Hk H. unfold fsT_ret_regions, pic_rs_ps, pic_rs. cbn [app regions_wf] in *.
rewrite andb_true_r in H. rewrite H.
rewrite (pic_blk_wf (xatom 16) (56 * cap')), (pic_blk_wf (xatom 17) (8 * cap')), (pic_blk_wf (xatom 20) (klen + 1))
  by lia.
vm_compute. reflexivity.
Qed.

(* ================= the regions of the resume ================= *)
Section rg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* struct pj_in at s0 = q, from pj_in_ok (its wr_at is the window's writability) *)
Lemma pic_q_ok : forall E m q text len p d tb,
  bv_unsigned (ew E 8) = q -> ew E (xatom 0) = Z_to_bv 64 p -> ew E (xatom 1) = Z_to_bv 64 (text + len) ->
  ew E (xatom 2) = Z_to_bv 64 d ->
  PjIn.pj_in_ok tfibsegs m q text len p d tb -> region_ok tfibsegs E m pig_q_region.
Proof.
intros E m q text len p d tb E8 X0 X1 X2 (H1 & H2 & H3 & (W0 & W1 & W2) & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
unfold region_ok, pig_q_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E8.
split; [lia|]. split; [lia|]. split; [intros o Ho; exact (W2 o Ho)|].
constructor; [|constructor; [|constructor; [|constructor]]].
- apply (fsw_pj_chunk8 tfibsegs _ _ q 0 _ p); [rewrite Z.add_0_r; split; [lia | exact H1] | rewrite fsw_SOff0; exact X0].
- apply (fsw_pj_chunk8 tfibsegs _ _ q 8 _ (text + len)); [split; [lia | exact H2] | rewrite fsw_SOff0; exact X1].
- apply (fsw_pj_chunk4 tfibsegs _ _ q 16 _ d); [split; [lia | exact H3] | rewrite fsw_SOff0; exact X2].
Qed.
(* the object v at s4 *)
Lemma pic_v_ok : forall E m v num str k' y' n cap',
  bv_unsigned (ew E 20) = v -> ew E (xatom 16) = Z_to_bv 64 k' -> ew E (xatom 17) = Z_to_bv 64 y' ->
  ew E (xatom 18) = Z_to_bv 64 n -> ew E (xatom 19) = Z_to_bv 64 cap' ->
  0 <= v -> v + 56 <= 2 ^ 64 -> (forall i, 0 <= i < 56 -> writable_at tfibsegs m (v + i)) ->
  PjStruct.pj_hdr tfibsegs m v 6 num str k' y' n cap' -> region_ok tfibsegs E m pig_v_region.
Proof.
intros E m v num str k' y' n cap' E20 X16 X17 X18 X19 Hv0 Hv1 Hw (_ & Hty & _ & _ & Hk & Hy & Hn & Hc).
apply (fsw_pj_part_okW tfibsegs _ _ 20 v v 0 56 0 56); [lia | lia | exact Hw | exact E20 | lia | lia | right; lia |].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- apply (fsw_pj_chunk4 tfibsegs _ _ v 0 (SLit 6) 6); [rewrite Z.add_0_r; exact Hty | reflexivity].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 24 _ k'); [exact Hk | rewrite fsw_SOff0; exact X16].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 32 _ y'); [exact Hy | rewrite fsw_SOff0; exact X17].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 40 _ n); [exact Hn | rewrite fsw_SOff0; exact X18].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 48 _ cap'); [exact Hc | rewrite fsw_SOff0; exact X19].
Qed.
(* a byte window at an atom (a live block's body) *)
Lemma pic_blk_ok : forall E m a b len, bv_unsigned (ew E a) = b -> 0 <= b -> b + len <= 2 ^ 64 ->
  (forall i, 0 <= i < len -> writable_at tfibsegs m (b + i)) -> region_ok tfibsegs E m (pic_blk_region a len).
Proof.
intros E m a b len Eb Hb0 Hb1 Hw. unfold region_ok, pic_blk_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Eb.
split; [lia|]. split; [lia|]. split; [exact Hw | constructor].
Qed.
(* the pairwise disjointness of the resume regions: the frame [sp, sp + 144) and q above alloc_ceiling, the objects
   below it and off the image, v / kids / keys pairwise apart *)
Lemma pic_disj : forall E cs cap' sp q v k' y',
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 8) = q -> bv_unsigned (ew E 20) = v ->
  bv_unsigned (ew E (xatom 16)) = k' -> bv_unsigned (ew E (xatom 17)) = y' ->
  0x7fff7f800000 <= sp -> sp + 144 <= q -> q + 24 <= 2 ^ 47 ->
  4096 <= v -> v + 56 <= sp -> 4096 <= k' -> k' + 56 * cap' <= sp -> 4096 <= y' -> y' + 8 * cap' <= sp ->
  0 <= cap' ->
  pghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v) -> pghide (k' + 56 * cap' <= 0x10000 \/ FS_IMG_END <= k') ->
  pghide (y' + 8 * cap' <= 0x10000 \/ FS_IMG_END <= y') ->
  pghide (v + 56 <= k' \/ k' + 56 * cap' <= v) -> pghide (v + 56 <= y' \/ y' + 8 * cap' <= v) ->
  pghide (k' + 56 * cap' <= y' \/ y' + 8 * cap' <= k') ->
  pairwise_disjoint E (fsT_ret_regions 144 cs (pic_rs cap')).
Proof.
intros E cs cap' sp q v k' y' E2 E8 E20 E16 E17 Hsp Hq Hq1 Hv0 Hv1 Hk0 Hk1 Hy0 Hy1 Hc0 Iv Ik Iy Dvk Dvy Dky.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pic_rs, pig_q_region, pig_v_region, pic_blk_region.
cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E8, E20, E16, E17.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
repeat match goal with |- _ /\ _ => split end; try exact I; pic_pd.
Qed.
Lemma pic_disj_ps : forall E cs cap' klen sp q v k' y' a,
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 8) = q -> bv_unsigned (ew E 20) = v ->
  bv_unsigned (ew E (xatom 16)) = k' -> bv_unsigned (ew E (xatom 17)) = y' -> bv_unsigned (ew E (xatom 20)) = a ->
  0x7fff7f800000 <= sp -> sp + 144 <= q -> q + 24 <= 2 ^ 47 ->
  4096 <= v -> v + 56 <= sp -> 4096 <= k' -> k' + 56 * cap' <= sp -> 4096 <= y' -> y' + 8 * cap' <= sp ->
  4096 <= a -> a + (klen + 1) <= sp -> 0 <= cap' -> 0 <= klen ->
  pghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v) -> pghide (k' + 56 * cap' <= 0x10000 \/ FS_IMG_END <= k') ->
  pghide (y' + 8 * cap' <= 0x10000 \/ FS_IMG_END <= y') -> pghide (a + (klen + 1) <= 0x10000 \/ FS_IMG_END <= a) ->
  pghide (v + 56 <= k' \/ k' + 56 * cap' <= v) -> pghide (v + 56 <= y' \/ y' + 8 * cap' <= v) ->
  pghide (k' + 56 * cap' <= y' \/ y' + 8 * cap' <= k') -> pghide (v + 56 <= a \/ a + (klen + 1) <= v) ->
  pghide (k' + 56 * cap' <= a \/ a + (klen + 1) <= k') -> pghide (y' + 8 * cap' <= a \/ a + (klen + 1) <= y') ->
  pairwise_disjoint E (fsT_ret_regions 144 cs (pic_rs_ps cap' klen)).
Proof.
intros E cs cap' klen sp q v k' y' a E2 E8 E20 E16 E17 Ea Hsp Hq Hq1 Hv0 Hv1 Hk0 Hk1 Hy0 Hy1 Ha0 Ha1 Hc0 Hl0
  Iv Ik Iy Ia Dvk Dvy Dky Dva Dka Dya.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pic_rs_ps, pic_rs, pig_q_region, pig_v_region,
  pic_blk_region.
cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E8, E20, E16, E17, Ea.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
repeat match goal with |- _ /\ _ => split end; try exact I; pic_pd.
Qed.
(* the atom facts *)
Lemma pic_gf_ok : forall E q v p e d k' y' n cap',
  bv_unsigned (ew E 8) = q -> bv_unsigned (ew E 20) = v ->
  ew E (xatom 0) = Z_to_bv 64 p -> ew E (xatom 1) = Z_to_bv 64 e -> ew E (xatom 2) = Z_to_bv 64 d ->
  ew E (xatom 16) = Z_to_bv 64 k' -> ew E (xatom 17) = Z_to_bv 64 y' ->
  ew E (xatom 18) = Z_to_bv 64 n -> ew E (xatom 19) = Z_to_bv 64 cap' ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 ->
  4096 <= p <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 0 <= d <= 3 ->
  4096 <= k' <= 2 ^ 47 - 2 ^ 23 -> k' mod 16 = 0 -> 4096 <= y' <= 2 ^ 47 - 2 ^ 23 -> y' mod 16 = 0 ->
  0 <= n <= 2 ^ 54 -> 0 <= cap' <= 2 ^ 54 ->
  atoms_ok E pic_gf.
Proof.
intros E q v p e d k' y' n cap' E8 E20 X0 X1 X2 X16 X17 X18 X19 Hq Hq8 Hv Hv8 Hp He Hd Hk Hk16 Hy Hy16 Hn Hc.
unfold pic_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E8, E20, X0, X1, X2, X16, X17, X18, X19.
rewrite (wz p), (wz e), (wz d), (wz k'), (wz y'), (wz n), (wz cap') by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
repeat split; try lia; try apply Z.mod_1_r; assumption.
Qed.
Lemma pic_gf_ps_ok : forall E q v p e d k' y' n cap' a klen,
  bv_unsigned (ew E 8) = q -> bv_unsigned (ew E 20) = v ->
  ew E (xatom 0) = Z_to_bv 64 p -> ew E (xatom 1) = Z_to_bv 64 e -> ew E (xatom 2) = Z_to_bv 64 d ->
  ew E (xatom 16) = Z_to_bv 64 k' -> ew E (xatom 17) = Z_to_bv 64 y' ->
  ew E (xatom 18) = Z_to_bv 64 n -> ew E (xatom 19) = Z_to_bv 64 cap' ->
  ew E (xatom 20) = Z_to_bv 64 a -> ew E (xatom 21) = Z_to_bv 64 klen ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 ->
  4096 <= p <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 0 <= d <= 3 ->
  4096 <= k' <= 2 ^ 47 - 2 ^ 23 -> k' mod 16 = 0 -> 4096 <= y' <= 2 ^ 47 - 2 ^ 23 -> y' mod 16 = 0 ->
  0 <= n <= 2 ^ 54 -> 0 <= cap' <= 2 ^ 54 -> 4096 <= a <= 2 ^ 47 - 2 ^ 23 -> 0 <= klen <= 2 ^ 54 ->
  atoms_ok E pic_gf_ps.
Proof.
intros E q v p e d k' y' n cap' a klen E8 E20 X0 X1 X2 X16 X17 X18 X19 X20 X21 Hq Hq8 Hv Hv8 Hp He Hd Hk Hk16 Hy Hy16
  Hn Hc Ha Hl.
unfold pic_gf_ps, pic_gf. cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E8, E20, X0, X1, X2, X16, X17, X18, X19, X20, X21.
rewrite (wz p), (wz e), (wz d), (wz k'), (wz y'), (wz n), (wz cap'), (wz a), (wz klen) by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
repeat split; try lia; try apply Z.mod_1_r; assumption.
Qed.
End rg.

(* ================= the T resume at a raised window top ================= *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pic_resumeT : forall B STK ot FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k regs2 sf f xs cs
  rs gf r (mk : word -> option byte),
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK ot FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  spZ regs2 = sf - f -> 0 < f -> (sf - f) mod 16 = 0 -> ot - STK <= sf - f -> sf <= ot ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) mk (sf - f)) cs ->
  (forall a, sf - f <= a < sf -> mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs mk a) ->
  Forall (region_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) mem2)) rs ->
  pairwise_disjoint (Ereg regs2 (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs2 (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK ot FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 sf f xs cs rs gf r mk
  Hgot Hcell HJ HARU Usp Hf Hal Hlo Hsf Hwf Hcs Hkeep Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hin : forall c, In c cs -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f).
{ pose proof Hwf as Hw. unfold fsT_ret_regions in Hw. cbn [app regions_wf] in Hw.
  apply andb_prop in Hw as [Hw _]. unfold YP09.region_wf in Hw.
  apply andb_prop in Hw as [_ Hfa]. rewrite forallb_forall in Hfa.
  intros c Hc. pose proof (Hfa c Hc) as Hci. unfold YP09.chunk_inside, fstk_ret in Hci.
  cbn [YP09.r_lo YP09.r_hi] in Hci. apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2]. }
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = sf - f)
  by (rewrite (ew_Ereg_nat regs2 (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs2 (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
destruct (fsw_got_shadow B lyc Sc W (unpoison U2 mem2) md2 Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U2 mem2)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B lyc Sc U2 W mem2 md2 (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U2 mem2)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U2 mem2) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U2 mem2) _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + (* the frame: present by the journal's window, its chunks on mk *)
    unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
    * apply Forall_forall. intros c Hc. destruct (Hin c Hc) as [Hc0 Hc1].
      apply (chunk_ok_mbyte _ mk); [|exact (proj1 (Forall_forall _ _) Hcs c Hc)].
      intros i Hi. apply Hkeep. lia.
  + unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia].
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
End t.

(* ================= kit facts of the three steps ================= *)
Section kf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* a live block's bytes are writable on the machine's memory *)
Lemma pic_block_writable : forall ly S U (W : world tfibsegs) mem md b nb x,
  ARU tfibsegs B ly S U W mem md -> In (b, nb) (ablocks B ly S) -> b <= x < b + req_size nb ->
  writable_at tfibsegs (mrestrict (w_H W) mem) x.
Proof.
intros ly S U W mem md b nb x HU Hin Hx. pose proof HU as (HAR & _ & _).
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md b nb HAR Hin)
  as (_ & _ & _ & _ & HP & _).
destruct (proj1 (HP x Hx)) as (Hh & c & Hc).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md b nb HAR Hin) as (A1 & A2 & _). pose proof asan_consts as (C1 & _).
rewrite (fsw_unpoison_app B ly S U W mem md x HU ltac:(lia)
  (fsw_ablock_off_shadow B ly S W (unpoison U mem) md b nb HAR Hin x Hx)) in Hc.
apply (apresent_writable tfibsegs). split; [exact Hh | exists c; exact Hc].
Qed.
(* writability follows the raw byte *)
Lemma pic_writable_eq : forall (m m' : word -> option byte) x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  writable_at tfibsegs m x -> writable_at tfibsegs m' x.
Proof. intros m m' x E H. unfold writable_at, wview in *. rewrite E. exact H. Qed.
(* a reader block across a callee journal whose footprint misses its 8-byte head *)
Lemma pic_rblock_kept : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc p k,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x, p - HEAD <= x < p - HEAD + 8 -> ~ inFP FP1 x) ->
  fs_rblock tfibsegs B lyc Sc W memc p k -> fs_rblock tfibsegs B ly' S' W' mem' p k.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc p k HJ HU HO' HP' HF (Hin & Hal & Hk & Hv).
pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
split; [|split; [exact Hal | split; [exact Hk|]]].
- apply (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
    (p - HEAD) (k + HEAD) (p - HEAD) HJ Hin); [unfold HEAD in *; lia | apply HF; lia].
- intros j Hj.
  assert (E : mrestrict (w_H W') mem' (Z_to_bv 64 (p - HEAD + Z.of_nat j)) =
              mrestrict (w_H W) memc (Z_to_bv 64 (p - HEAD + Z.of_nat j))).
  { refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ HJ HU HO' HP' _ _)).
    - left. exists (p - HEAD), (k + HEAD). split; [exact Hin | unfold HEAD in *; cbn in Hj; lia].
    - apply HF. cbn in Hj. lia. }
  unfold mbyte. rewrite E. exact (Hv j Hj).
Qed.
(* where a pobj's 56 bytes lie: in a block of the state or a frame of it *)
Lemma pic_pobj_place : forall ly S (W : world tfibsegs) m v, pobj tfibsegs B ly S W m v ->
  forall x, v <= x < v + 56 ->
    (exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n) \/
    (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S W m v HP x Hx.
destruct HP as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] _].
- right. exists cid, pos. split; [exact Hin | lia].
- left. exists b, n. split; [exact Hin | unfold HEAD in H1; lia].
Qed.
(* a byte of a block or a frame of an AR state is no image byte *)
Lemma pic_noimg : forall ly S (W : world tfibsegs) mx md x, AR tfibsegs B ly S W mx md ->
  ((exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid)) ->
  ~ in_img tfibsegs x.
Proof.
intros ly S W mx md x HAR [(p & n & Hin & Hr)|(cid & pos & Hin & Hr)].
- exact (blk_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md p n x HAR Hin Hr).
- exact (frm_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md cid pos x HAR Hin Hr).
Qed.
(* the kids and keys blocks of the object v at a call: live reader blocks, below alloc_ceiling, off the image,
   pairwise apart and apart from v *)
Lemma pic_blk_facts : forall ly S (W : world tfibsegs) mx md m v k' y' n cap',
  AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v -> n < cap' -> 0 <= n ->
  rd_blocks_ok tfibsegs B ly S W m (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  PjStruct.pj_apart (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') v ->
  ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap' = [(k', 56 * cap'); (y', 8 * cap')] /\
  fs_rblock tfibsegs B ly S W m k' (56 * cap') /\ fs_rblock tfibsegs B ly S W m y' (8 * cap') /\
  4096 + HEAD <= k' /\ k' + 56 * cap' <= alloc_ceiling /\ 4096 + HEAD <= y' /\ y' + 8 * cap' <= alloc_ceiling /\
  k' mod 16 = 0 /\ y' mod 16 = 0 /\
  pghide (k' + 56 * cap' <= 0x10000 \/ FS_IMG_END <= k') /\ pghide (y' + 8 * cap' <= 0x10000 \/ FS_IMG_END <= y') /\
  pghide (v + 56 <= k' \/ k' + 56 * cap' <= v) /\ pghide (v + 56 <= y' \/ y' + 8 * cap' <= v) /\
  pghide (k' + 56 * cap' <= y' \/ y' + 8 * cap' <= k') /\
  pghide (k' + 56 * cap' <= y' - HEAD \/ y' + 8 * cap' <= k' - HEAD).
Proof.
intros ly S W mx md m v k' y' n cap' HAR HPO Hn Hn0 HBLK HAP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (E : ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap' = [(k', 56 * cap'); (y', 8 * cap')])
  by (unfold ReaderRes.kids_blk, ReaderRes.keys_blk; rewrite (proj2 (Z.eqb_neq cap' 0)) by lia; reflexivity).
rewrite E in HBLK, HAP.
pose proof (HBLK k' (56 * cap') ltac:(left; reflexivity)) as KRB.
pose proof (HBLK y' (8 * cap') ltac:(right; left; reflexivity)) as YRB.
destruct (fsw_rblock_low B ly S W mx md m k' _ HAR KRB) as (K1 & K2).
destruct (fsw_rblock_low B ly S W mx md m y' _ HAR YRB) as (Y1 & Y2).
pose proof KRB as (KIN & Kal & _ & _). pose proof YRB as (YIN & Yal & _ & _).
pose proof (fsw_ablock_off_img B ly S W mx md _ _ HAR KIN) as Ki.
pose proof (fsw_ablock_off_img B ly S W mx md _ _ HAR YIN) as Yi.
rewrite FSW_grow_holds.grow_req in Ki, Yi by lia.
pose proof (FSW_grow_holds.grow_v_off_rblk B ly S W mx md m v k' (56 * cap') HAR HPO KIN ltac:(lia)
  (fun b x Hb Hx => HAP b x ltac:(destruct Hb as [<-|[]]; left; reflexivity) Hx)) as VK.
pose proof (FSW_grow_holds.grow_v_off_rblk B ly S W mx md m v y' (8 * cap') HAR HPO YIN ltac:(lia)
  (fun b x Hb Hx => HAP b x ltac:(destruct Hb as [<-|[]]; right; left; reflexivity) Hx)) as VY.
assert (Ap : forall a la b lb, 0 < la -> 0 < lb -> (forall x, a <= x < a + la -> ~ (b <= x < b + lb)) ->
  a + la <= b \/ b + lb <= a).
{ intros a la b lb H1 H2 H. destruct (Z_le_gt_dec (a + la) b) as [|Hb]; [left; lia|].
  destruct (Z_le_gt_dec (b + lb) a) as [|Ha]; [right; lia|]. exfalso. apply (H (Z.max a b)); lia. }
pose proof (Ap v 56 (k' - HEAD) (56 * cap' + HEAD) ltac:(lia) ltac:(unfold HEAD; lia)
  ltac:(intros x Hx; replace (k' - HEAD + (56 * cap' + HEAD)) with (k' + 56 * cap') by lia; exact (VK x Hx))) as DVK.
pose proof (Ap v 56 (y' - HEAD) (8 * cap' + HEAD) ltac:(lia) ltac:(unfold HEAD; lia)
  ltac:(intros x Hx; replace (y' - HEAD + (8 * cap' + HEAD)) with (y' + 8 * cap') by lia; exact (VY x Hx))) as DVY.
pose proof (sep_blocks tfibsegs B LAWS ly S W mx md _ _ _ _ HAR KIN YIN
  ltac:(intros Eq; injection Eq as _ Eq; lia)) as DKY.
unfold zdisjoint in DKY. cbn [fst snd] in DKY. rewrite !FSW_grow_holds.grow_req in DKY by lia.
unfold pghide. unfold HEAD in *.
split; [exact E|]. split; [exact KRB|]. split; [exact YRB|].
repeat split; try lia; try exact Kal; try exact Yal.
Qed.
End kf.

(* ================= parse_items' parse_string call, the key (0x84c4c -> 0x84c50) ================= *)
Section ps. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells (FSH_Base.v); FSrtcellsS0.fs_shadow_syms_of discharges it at ENTRY's composition *)
Hypothesis HSS : FsShadowSyms B.
(* callee: parse_string (S0, lib/A/FSW_parse_string.v parse_string_proof) *)
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.

(* the call at ra 0x84c50: a0 = s0 = q (the only argument). Premises beyond grow's: in->depth d <= 3 (gf),
   parse_string's own (the quote byte 34 at in->p, the plain run of Qk bytes, the allocation budget), n < cap' (the
   member slot exists), the frame chain at s0 = q on the call memory (parse_string's C5 premise and fuzz_malloc's
   fpreU read it), and region_wf of the frame region alone. *)
Definition pic_ps_at : Prop :=
  forall (m : nat) sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC ch q text len p d (tb : list byte) tcap
    xr v num str k' y' n cap' Qk live peak cnt fail cs (Qc : world tfibsegs -> config -> Prop),
  let FP := [(v, v + 56)] ++ FS_PSTAT_FP in
  let Dk := ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap' in
  ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    lyc Sc W (unpoison Uc memC) mdC kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B lyc Sc Uc ->
  YK11.getr regsC 1 = w64 0x84c50 -> spZ regsC = sp0 - 144 -> sp0 mod 16 = 0 -> sp0 <= ot ->
  YK11.getr regsC 8 = w64 q -> YK11.getr regsC 20 = w64 v -> YK11.getr regsC 10 = w64 q ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison Uc memC)) (spZ regsC) q ch ->
  sp0 <= q -> q + 24 <= ot ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb -> d <= 3 ->
  rd_text tfibsegs B lyc Sc W memC text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) -> plain_run tb text len p Qk ->
  length xr = 13%nat ->
  pobj tfibsegs B lyc Sc W memC v -> PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) memC) v 6 num str k' y' n cap' ->
  n < cap' -> rd_blocks_ok tfibsegs B lyc Sc W memC Dk -> PjStruct.pj_apart Dk v ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail 1 ->
  Qk + 1 + HEAD < MALLOC_MAX -> live + Qk + 1 < 2 ^ 64 ->
  st_nev Sc + EV_fuzz_malloc <= EV_MAX -> blocks_bytes Sc + (Qk + 1 + HEAD) <= LIVE_MAX ->
  regions_wf [fstk_ret 144 cs] = true ->
  (forall regs' a, aregs_preserved regsC regs' ->
     Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ pic_xs_ps (p + Qk + 2) (text + len) d xr k' y' n cap' a Qk))
       (mrestrict (w_H W) memC) (sp0 - 144)) cs) ->
  (forall a ly' S' W' regs' mem' md',
     ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
       ly' S' W' (unpoison (Uc ++ [(a - HEAD, HEAD)]) mem') md' (kc + EV_fuzz_malloc) ->
     ajournal tfibsegs B (STK_parse_string + (ot - spZ regsC)) ot FS_PSTAT_FP lyc Sc W (unpoison Uc memC) mdC []
       ly' S' W' (unpoison (Uc ++ [(a - HEAD, HEAD)]) mem') md' EV_fuzz_malloc ->
     ARU tfibsegs B ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' mem' md' ->
     aregs_preserved regsC regs' -> YK11.getr regs' 10 = w64 a ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pic_xs_ps (p + Qk + 2) (text + len) d xr k' y' n cap' a Qk))
       (fss_retT 0x84c50 144 cs (pic_rs_ps cap' Qk) pic_gf_ps)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84c50) mem' (seg_rom tfibsegs))) ->
     4096 + HEAD <= a -> ablocks B ly' S' = ablocks B lyc Sc ++ [(a - HEAD, Qk + 1 + HEAD)] ->
     fs_rblock tfibsegs B ly' S' W' mem' a (Qk + 1) ->
     PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a (run_at tb text p Qk) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Qk + 2) d tb ->
     wkeep tfibsegs W W' memC mem' (spZ regsC) ot q 24 ->
     rd_text tfibsegs B ly' S' W' mem' text len tcap ->
     fs_glob tfibsegs W' mem' (live + Qk + 1) (Z.max peak (live + Qk + 1)) (cnt + 1) fail ->
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 num str k' y' n cap' ->
     (forall x, v <= x < v + 56 -> mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x) ->
     rd_blocks_ok tfibsegs B ly' S' W' mem' Dk ->
     (forall x, k' <= x < k' + 56 * cap' \/ y' <= x < y' + 8 * cap' ->
        mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x84c50) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_string regsC memC mdC) Qc.

Lemma pic_call_ps_84c4c : pic_ps_at.
Proof.
intros m sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC ch q text len p d tb tcap xr v num str k' y' n
  cap' Qk live peak cnt fail cs Qc FP Dk HJ HARU HRO HHEADS R1 Rsp Hal0 Hot R8 R20 R10 R3 R4 HCH Hq0 Hq1 HIN Hd3 HTX
  Hplt Hnth Hrun Hxr HPO HHDR Hncap HBLK HAPART HG HQ HMAX HLIVE HEV HLV HWF HCS K.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HARU as (HAR & _ & _).
assert (HSTK : STK_parse_string + 144 <= STK_parse_items m)
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
assert (HSTK0 : 0 <= STK_parse_string)
  by (unfold STK_parse_string, zmaxl, FRAME_parse_string; cbn [fold_right]; lia).
assert (Wv : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; unfold w64; apply wz; exact Hz).
destruct (fsw_pobj_low B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO) as (Lv1 & Lv2).
assert (Hvimg : pghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v))
  by exact (fsw_pobj_off_img B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Ha & _)|(_ & Ha & _)] _]; exact Ha).
pose proof HHDR as (_ & _ & _ & _ & _ & _ & (Hn0 & _) & (Hc0 & _)).
assert (HH : HEAD = 16) by reflexivity.
destruct (pic_blk_facts B lyc Sc W (unpoison Uc memC) mdC memC v k' y' n cap' HAR HPO Hncap ltac:(lia) HBLK HAPART)
  as (EDk & KRB & YRB & KL1 & KL2 & YL1 & YL2 & Kal & Yal & Ki & Yi & Dvk & Dvy & Dky & DkyH).
assert (KinDk : In (k', 56 * cap') Dk) by (unfold Dk; rewrite EDk; left; reflexivity).
assert (YinDk : In (y', 8 * cap') Dk) by (unfold Dk; rewrite EDk; right; left; reflexivity).
pose proof HTX as (Ht0 & TRB & Htl).
destruct (fsw_rblock_low B lyc Sc W (unpoison Uc memC) mdC memC text tcap HAR TRB) as (T1 & T2).
pose proof HIN as (_ & _ & _ & _ & Hq8 & _ & _ & Hpp & _ & _ & _ & Hd0).
pose proof Hrun as (HQ0 & _).
(* ---- parse_string's fpreU and its window at the call ---- *)
assert (PRE : fpreU tfibsegs B STK_parse_string lyc Sc Uc W regsC memC mdC ch).
{ apply (fsw_fpreU_atFP B (STK_parse_items m + (ot - sp0)) ot FP ly S Uc W0 (unpoison U0 mem0) md0 own lyc Sc W memC mdC kc
    regsC STK_parse_string (sp0 - 144 - ot) ch HJ HARU HRO).
  - rewrite Rsp. lia.
  - clear - Hal0 Hal16. Z.div_mod_to_equations. lia.
  - lia.
  - exact HSTK0.
  - lia.
  - rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
  - unfold raZ. rewrite R1, Wv by lia. lia.
  - exact R3.
  - exact R4.
  - unfold s0Z. rewrite R8, Wv by lia. exact HCH. }
assert (HWIN : rd_win tfibsegs regsC lyc W memC q ot).
{ unfold rd_win. rewrite Rsp. split; [lia|]. split; [lia|]. split; [exact Hal16|]. split; [rewrite Etop; exact Htop|].
  intros a0 Ha0. apply (fsw_apresent_unpoison B lyc Sc Uc W memC mdC a0 HARU); [lia|]. apply Hpres. lia. }
(* ---- the call ---- *)
eapply SRr_bind.
{ apply (HPS lyc Sc Uc W regsC memC mdC ch q ot text len p d tb tcap Qk live peak cnt fail PRE HHEADS).
  - exists ch. apply (achain_lower _ _ (spZ regsC)); [exact HCH | unfold FRAME_parse_string; lia].
  - rewrite Rsp. lia.
  - exact R10.
  - exact HIN.
  - exact HWIN.
  - exact HTX.
  - exact Hplt.
  - exact Hnth.
  - exact Hrun.
  - exact HG.
  - exact HQ.
  - exact HMAX.
  - exact HLIVE.
  - exact HEV.
  - exact HLV. }
intros W' c' _ (a & ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP &
  (A10 & Ha16 & Hab & HRB & HCB & HIN' & HWK & HTX' & HG')).
(* ---- the composed journal ---- *)
assert (HFPS : fsw_fp_sub B ly S lyc Sc own FP FS_PSTAT_FP).
{ intros a0 Ha0. right; right; left. split; [unfold FP; apply inFP_app; right; exact Ha0 | exact (pig_pstat_img a0 Ha0)]. }
set (U' := Uc ++ [(a - HEAD, HEAD)]) in *.
assert (I1 : ot - (STK_parse_items m + (ot - sp0)) <= ot - (STK_parse_string + (ot - spZ regsC))) by (rewrite Rsp; lia).
assert (HJ2 : ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    ly' S' W' (unpoison U' mem') md' (kc + EV_fuzz_malloc))
  by exact (fsw_ajournal_sub5 B _ ot FP ly S W0 (unpoison U0 mem0) md0 own lyc Sc W (unpoison Uc memC) mdC kc
              _ ot FS_PSTAT_FP [] ly' S' W' (unpoison U' mem') md' _ HJ HJc I1 (Z.le_refl ot) HFPS).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
pose proof HJc as (HARc' & Hlyc & _ & _ & _ & Hfrc & _).
(* ---- what parse_string keeps: every block / frame byte of the call (FS_PSTAT_FP is image bytes) ---- *)
assert (NFP : forall x, ~ in_img tfibsegs x -> ~ inFP FS_PSTAT_FP x) by (intros x Hx Hf; exact (Hx (pig_pstat_img x Hf))).
assert (KB : forall x, ((exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= x < p0 + req_size n0) \/
      (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
   mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x)).
{ intros x Hx. refine (proj2 (fsw_journal_kept_byte B _ _ _ lyc Sc Uc W memC mdC ly' S' U' W' mem' md' _ x HJc HARU OK' PO' Hx _)).
  exact (NFP x (pic_noimg B lyc Sc W (unpoison Uc memC) mdC x HAR Hx)). }
assert (VB : forall x, v <= x < v + 56 -> mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x))
  by (intros x Hx; apply KB; exact (pic_pobj_place B lyc Sc W memC v HPO x Hx)).
assert (VBm : forall x, v <= x < v + 56 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x)
  by (intros x Hx; unfold mbyte; rewrite (VB x Hx); reflexivity).
assert (HHDR' : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 num str k' y' n cap').
{ apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) memC)); [exact HHDR|].
  intros x Hx. exact (FSW_grow_holds.grow_word_eq _ _ (fun z => v <= z < v + 56) x VB Hx). }
assert (VW' : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i)).
{ intros i Hi. apply (pic_writable_eq (mrestrict (w_H W) memC)); [exact (VB (v + i) ltac:(lia)) | exact (proj2 HPO i Hi)]. }
assert (BLK' : rd_blocks_ok tfibsegs B ly' S' W' mem' Dk).
{ apply (rd_blocks_ok_kept_call B _ _ _ lyc Sc Uc W memC mdC ly' S' U' W' mem' md' _ Dk HJc HARU OK' PO'); [|exact HBLK].
  intros a0 k0 x Hak Hx. apply NFP. pose proof (HBLK a0 k0 Hak) as (Hin & _ & Hk0 & _).
  apply (blk_img tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC _ _ x HAR Hin).
  rewrite FSW_grow_holds.grow_req by lia. unfold HEAD in *. lia. }
assert (KBm : forall x, k' <= x < k' + 56 * cap' \/ y' <= x < y' + 8 * cap' ->
   mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x).
{ intros x Hx. unfold mbyte. rewrite KB; [reflexivity|]. left.
  destruct Hx as [Hx|Hx]; [exists (k' - HEAD), (56 * cap' + HEAD) | exists (y' - HEAD), (8 * cap' + HEAD)].
  - split; [exact (proj1 KRB) | rewrite FSW_grow_holds.grow_req by lia; unfold HEAD; lia].
  - split; [exact (proj1 YRB) | rewrite FSW_grow_holds.grow_req by lia; unfold HEAD; lia]. }
pose proof (proj1 (BLK' k' (56 * cap') KinDk)) as KIN'. pose proof (proj1 (BLK' y' (8 * cap') YinDk)) as YIN'.
(* ---- the key block ---- *)
pose proof HRB as (AIN' & Aal & _ & _).
destruct (fsw_rblock_low B ly' S' W' (unpoison U' mem') md' mem' a _ HARc' HRB) as (A1 & A2).
assert (Hnew : ~ In (a - HEAD, Qk + 1 + HEAD) (ablocks B lyc Sc)).
{ intros Hin. apply (FSW_grow_holds.grow_blk_nodup B ly' S' W' _ md' (ablocks B lyc Sc) [] (a - HEAD, Qk + 1 + HEAD) HARc');
    [rewrite Hab; reflexivity | rewrite app_nil_r; exact Hin]. }
assert (Ai : pghide (a + (Qk + 1) <= 0x10000 \/ FS_IMG_END <= a)).
{ pose proof (fsw_ablock_off_img B ly' S' W' _ md' _ _ HARc' AIN') as H.
  rewrite FSW_grow_holds.grow_req in H by lia. unfold pghide, HEAD in *. lia. }
assert (Dka : pghide (k' + 56 * cap' <= a \/ a + (Qk + 1) <= k')).
{ assert (Hne : (k' - HEAD, 56 * cap' + HEAD) <> (a - HEAD, Qk + 1 + HEAD))
    by (intros E; apply Hnew; rewrite <- E; exact (proj1 KRB)).
  pose proof (sep_blocks tfibsegs B LAWS ly' S' W' _ md' _ _ _ _ HARc' KIN' AIN' Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !FSW_grow_holds.grow_req in D by lia. unfold pghide, HEAD in *. lia. }
assert (Dya : pghide (y' + 8 * cap' <= a \/ a + (Qk + 1) <= y')).
{ assert (Hne : (y' - HEAD, 8 * cap' + HEAD) <> (a - HEAD, Qk + 1 + HEAD))
    by (intros E; apply Hnew; rewrite <- E; exact (proj1 YRB)).
  pose proof (sep_blocks tfibsegs B LAWS ly' S' W' _ md' _ _ _ _ HARc' YIN' AIN' Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !FSW_grow_holds.grow_req in D by lia. unfold pghide, HEAD in *. lia. }
assert (Dva : pghide (v + 56 <= a \/ a + (Qk + 1) <= v)).
{ unfold pghide.
  destruct (Z_le_gt_dec (v + 56) a) as [|H1]; [left; lia|]. destruct (Z_le_gt_dec (a + (Qk + 1)) v) as [|H2]; [right; lia|].
  exfalso. set (x := Z.max v a).
  destruct (pic_pobj_place B lyc Sc W memC v HPO x ltac:(unfold x; lia)) as [(p0 & n0 & Hin & Hr0)|(cid & pos & Hin & Hr0)].
  - assert (Hin' : In (p0, n0) (ablocks B ly' S')).
    { apply (fsw_journal_block_live B _ _ _ lyc Sc W (unpoison Uc memC) mdC ly' S' W' (unpoison U' mem') md' _ p0 n0 x HJc
        Hin Hr0).
      exact (NFP x (blk_img tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC p0 n0 x HAR Hin Hr0)). }
    assert (Hne : (p0, n0) <> (a - HEAD, Qk + 1 + HEAD)) by (intros E; rewrite E in Hin; exact (Hnew Hin)).
    pose proof (sep_blocks tfibsegs B LAWS ly' S' W' _ md' p0 n0 _ _ HARc' Hin' AIN' Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite FSW_grow_holds.grow_req in D by lia. unfold x, HEAD in *. lia.
  - assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrc; exact Hin).
    pose proof (sep_block_frame tfibsegs B LAWS ly' S' W' _ md' _ _ cid pos HARc' AIN' Hin') as D.
    pose proof Hlyc as (_ & _ & _ & _ & _ & HF' & _). unfold zdisjoint, frame_addr in *. cbn [fst snd] in D.
    rewrite HF' in D. rewrite FSW_grow_holds.grow_req in D by lia. unfold x, HEAD in *. lia. }
(* ---- the resume env ---- *)
set (P' := p + Qk + 2) in *.
set (xs := pic_xs_ps P' (text + len) d xr k' y' n cap' a Qk).
set (E := Ereg regs' (fs_extraT ++ xs)).
assert (G8 : YK11.getr regs' 8 = w64 q) by (rewrite <- R8; exact (HP 8 ltac:(unfold acallee_saved; lia))).
assert (G20 : YK11.getr regs' 20 = w64 v) by (rewrite <- R20; exact (HP 20 ltac:(unfold acallee_saved; lia))).
assert (G2 : YK11.getr regs' 2 = YK11.getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp' : spZ regs' = sp0 - 144) by (unfold spZ; rewrite G2; exact Rsp).
assert (E8 : bv_unsigned (ew E 8) = q) by (unfold E; rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), G8; apply Wv; lia).
assert (E20 : bv_unsigned (ew E 20) = v) by (unfold E; rewrite (ew_Ereg_nat regs' _ 20 20%bv eq_refl), G20; apply Wv; lia).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 144) by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Usp').
destruct (pic_xs_ps_nth P' (text + len) d xr k' y' n cap' a Qk Hxr) as (XL & X20 & X21).
destruct (pig_xs_nth P' (text + len) d xr k' y' n cap' Hxr) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
assert (XA : forall j, (j < 20)%nat -> ew E (xatom j) = nth j (pig_xs P' (text + len) d xr k' y' n cap') (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite fsw_ew_xatom; unfold xs; exact (XL j Hj)).
assert (Y0 : ew E (xatom 0) = Z_to_bv 64 P') by (rewrite (XA 0%nat ltac:(lia)); exact X0).
assert (Y1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite (XA 1%nat ltac:(lia)); exact X1).
assert (Y2 : ew E (xatom 2) = Z_to_bv 64 d) by (rewrite (XA 2%nat ltac:(lia)); exact X2).
assert (Y16 : ew E (xatom 16) = Z_to_bv 64 k') by (rewrite (XA 16%nat ltac:(lia)); exact X16).
assert (Y17 : ew E (xatom 17) = Z_to_bv 64 y') by (rewrite (XA 17%nat ltac:(lia)); exact X17).
assert (Y18 : ew E (xatom 18) = Z_to_bv 64 n) by (rewrite (XA 18%nat ltac:(lia)); exact X18).
assert (Y19 : ew E (xatom 19) = Z_to_bv 64 cap') by (rewrite (XA 19%nat ltac:(lia)); exact X19).
assert (Y20 : ew E (xatom 20) = Z_to_bv 64 a) by (unfold E; rewrite fsw_ew_xatom; unfold xs; exact X20).
assert (Y21 : ew E (xatom 21) = Z_to_bv 64 Qk) by (unfold E; rewrite fsw_ew_xatom; unfold xs; exact X21).
pose proof HIN' as (_ & _ & _ & _ & _ & _ & _ & HPp & _).
unfold MALLOC_MAX in HMAX.
(* ---- the resume regions ---- *)
assert (HRSOK : Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) (pic_rs_ps cap' Qk)).
{ unfold pic_rs_ps, pic_rs. cbn [app].
  constructor; [exact (pic_q_ok E _ q text len P' d tb E8 Y0 Y1 Y2 HIN')|].
  constructor; [exact (pic_v_ok E _ v num str k' y' n cap' E20 Y16 Y17 Y18 Y19 ltac:(lia) ltac:(lia) VW' HHDR')|].
  constructor.
  { apply (pic_blk_ok E _ (xatom 16) k'); [rewrite Y16; apply wz; lia | lia | lia |]. intros i Hi.
    apply (pic_block_writable B ly' S' U' W' mem' md' (k' - HEAD) (56 * cap' + HEAD)); [exact HARU' | exact KIN'|].
    rewrite FSW_grow_holds.grow_req by lia. unfold HEAD; lia. }
  constructor.
  { apply (pic_blk_ok E _ (xatom 17) y'); [rewrite Y17; apply wz; lia | lia | lia |]. intros i Hi.
    apply (pic_block_writable B ly' S' U' W' mem' md' (y' - HEAD) (8 * cap' + HEAD)); [exact HARU' | exact YIN'|].
    rewrite FSW_grow_holds.grow_req by lia. unfold HEAD; lia. }
  constructor; [|constructor].
  apply (pic_blk_ok E _ (xatom 20) a); [rewrite Y20; apply wz; lia | lia | lia |]. intros i Hi.
  apply (pic_block_writable B ly' S' U' W' mem' md' (a - HEAD) (Qk + 1 + HEAD)); [exact HARU' | exact AIN'|].
  rewrite FSW_grow_holds.grow_req by lia. unfold HEAD; lia. }
assert (HPD : pairwise_disjoint E (fsT_ret_regions 144 cs (pic_rs_ps cap' Qk))).
{ apply (pic_disj_ps E cs cap' Qk (sp0 - 144) q v k' y' a E2 E8 E20); try assumption;
    [rewrite Y16; apply wz; lia | rewrite Y17; apply wz; lia | rewrite Y20; apply wz; lia | ..]; lia. }
assert (HGF : atoms_ok E pic_gf_ps).
{ apply (pic_gf_ps_ok E q v P' (text + len) d k' y' n cap' a Qk E8 E20 Y0 Y1 Y2 Y16 Y17 Y18 Y19 Y20 Y21);
    first [exact Hq8 | exact Hv8 | exact Kal | exact Yal | lia]. }
(* ---- the resume ---- *)
assert (HKEEP : forall x, sp0 - 144 <= x < sp0 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x)
  by (intros x Hx; exact (proj1 (HWK x ltac:(rewrite Rsp; lia) ltac:(lia)))).
pose proof (pic_resumeT B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own ly' S' U' W' mem' md'
  (kc + EV_fuzz_malloc) regs' sp0 144 xs cs (pic_rs_ps cap' Qk) pic_gf_ps 0x84c50 (mrestrict (w_H W) memC)
  (proj1 HSS) (proj2 HSS) HJ2 HARU' Usp' ltac:(lia) ltac:(clear - Hal0; Z.div_mod_to_equations; lia) ltac:(lia) Hot
  (pic_wf_ps cs cap' Qk ltac:(lia) ltac:(lia) HWF) (HCS regs' a HP) HKEEP HRSOK HPD HGF) as HST.
rewrite R1.
exact (K a ly' S' W' regs' mem' md' HJ2 HJc HARU' HP A10 HST Ha16 Hab HRB HCB HIN' HWK HTX' HG' HHDR' VBm BLK' KBm).
Qed.
End ps.

(* ================= helpers of the memset and parse_value steps ================= *)
Section kf2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs.asan's image bytes lie in [0x10000, FS_IMG_END) *)
Lemma pic_img_lo : forall x, in_img tfibsegs x -> 0x10000 <= x < FS_IMG_END.
Proof.
intros x Hx. pose proof (fs_segs_img x Hx) as Hu. split; [|lia].
destruct Hx as (s & Hs & Hr).
assert (HB : forallb (fun s => 0x10000 <=? Z.of_N (seg_base s)) tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB s Hs) as Hc. cbv beta in Hc. apply Z.leb_le in Hc. lia.
Qed.
(* a reader block whose 8-byte head word is kept *)
Lemma pic_rblock_keep_raw : forall ly S (W : world tfibsegs) m m' p k,
  fs_rblock tfibsegs B ly S W m p k ->
  (forall x, p - HEAD <= x < p - HEAD + 8 -> mrestrict (w_H W) m' (Z_to_bv 64 x) = mrestrict (w_H W) m (Z_to_bv 64 x)) ->
  fs_rblock tfibsegs B ly S W m' p k.
Proof.
intros ly S W m m' p k (Hin & Hal & Hk & Hv) E. split; [exact Hin|]. split; [exact Hal|]. split; [exact Hk|].
intros j Hj. unfold mbyte. rewrite (E (p - HEAD + Z.of_nat j) ltac:(lia)). exact (Hv j Hj).
Qed.
(* a pobj whose bytes and shadow bytes are kept *)
Lemma pic_pobj_keep : forall ly S (W : world tfibsegs) m m' v, pobj tfibsegs B ly S W m v ->
  (forall i, 0 <= i < 56 -> mrestrict (w_H W) m' (Z_to_bv 64 (v + i)) = mrestrict (w_H W) m (Z_to_bv 64 (v + i))) ->
  (forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  0 <= v -> v + 56 <= alloc_ceiling -> pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' v HP Hb Hs Hv0 Hv1. pose proof asan_consts as (C1 & _).
assert (RA : range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF v 56 ->
             range_addressable (aview tfibsegs (w_H W) m') SHADOW_OFF v 56).
{ intros Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok]. rewrite <- Es. apply Hs.
  unfold shadow_of_addr. split; [|apply Zplus_lt_compat_l; apply Z.div_lt_upper_bound]; Z.div_mod_to_equations; lia. }
destruct HP as [Hpl Hw]. split.
- destruct Hpl as [(Hf & Ha & Hr)|(Hb' & Ha & Hr)]; [left | right]; (split; [assumption|]); (split; [exact Ha | exact (RA Hr)]).
- intros i Hi. exact (pic_writable_eq _ _ (v + i) (Hb i Hi) (Hw i Hi)).
Qed.
End kf2.

(* ================= parse_items' __asan_memset of the kid (0x84d78 -> 0x84d7c) ================= *)
Section ms. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* runtime callee: FSupoisonU's ARU form of the donor's __asan_memset contract at PC_memset 0x521bc (FSH_Fn_reader.v
   :54-56; S0's FsRt gives it as fr_memset) *)
Hypothesis MS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* the call at ra 0x84d7c: a0 = dk = kids' + 56 * n (the kid), a1 = 0, a2 = 56. Premises beyond grow's: in->depth
   d <= 3, the text block's request at the entry (the kids block is a temporary block, so the two differ), n < cap',
   tmp (the kids / keys blocks are not the entry's), region_wf of the frame region alone. *)
Definition pic_ms_at : Prop :=
  forall (m : nat) sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC q text len p d (tb : list byte) tcap
    xr v num str k' y' n cap' live peak cnt fail cs (Qc : world tfibsegs -> config -> Prop),
  let FP := [(v, v + 56)] ++ FS_PSTAT_FP in
  let Dk := ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap' in
  let dk := k' + 56 * n in
  ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    lyc Sc W (unpoison Uc memC) mdC kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> FSupoisonU.fs_heads B lyc Sc Uc ->
  YK11.getr regsC 1 = w64 0x84d7c -> spZ regsC = sp0 - 144 -> sp0 mod 16 = 0 -> sp0 <= ot ->
  YK11.getr regsC 8 = w64 q -> YK11.getr regsC 20 = w64 v ->
  YK11.getr regsC 10 = w64 dk -> YK11.getr regsC 11 = w64 0 -> YK11.getr regsC 12 = w64 56 ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  sp0 <= q -> q + 24 <= ot ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb -> d <= 3 ->
  rd_text tfibsegs B lyc Sc W memC text len tcap -> In (text - HEAD, tcap + HEAD) (ablocks B ly S) ->
  length xr = 13%nat ->
  pobj tfibsegs B lyc Sc W memC v -> PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) memC) v 6 num str k' y' n cap' ->
  n < cap' -> rd_blocks_ok tfibsegs B lyc Sc W memC Dk -> PjStruct.pj_apart Dk v ->
  (forall b, In b (rd_hblocks Dk) -> ~ In b (ablocks B ly S)) ->
  fs_glob tfibsegs W memC live peak cnt fail ->
  regions_wf [fstk_ret 144 cs] = true ->
  (forall regs', aregs_preserved regsC regs' ->
     Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ pig_xs p (text + len) d xr k' y' n cap'))
       (mrestrict (w_H W) memC) (sp0 - 144)) cs) ->
  (forall regs2 mem2 md2,
     ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
       lyc Sc W (unpoison Uc mem2) md2 kc ->
     ARU tfibsegs B lyc Sc Uc W mem2 md2 ->
     aregs_preserved regsC regs2 -> YK11.getr regs2 10 = w64 dk ->
     st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pig_xs p (text + len) d xr k' y' n cap'))
       (fss_retT 0x84d7c 144 cs (pic_rs cap') pic_gf)
       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x84d7c) mem2 (seg_rom tfibsegs))) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (dk <= a < dk + 56) -> ~ (spZ regsC - ESTACK <= a < spZ regsC) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memC a) ->
     PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem2) dk -> pobj tfibsegs B lyc Sc W mem2 dk ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem2) q text len p d tb ->
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem2) v 6 num str k' y' n cap' -> pobj tfibsegs B lyc Sc W mem2 v ->
     (forall x, q <= x < q + 24 \/ v <= x < v + 56 ->
        mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) memC) x) ->
     rd_blocks_ok tfibsegs B lyc Sc W mem2 Dk -> rd_text tfibsegs B lyc Sc W mem2 text len tcap ->
     fs_glob tfibsegs W mem2 live peak cnt fail ->
     SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x84d7c) mem2 (seg_rom tfibsegs)) md2) Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs PC_memset regsC memC mdC) Qc.

Lemma pic_call_ms_84d78 : pic_ms_at.
Proof.
intros m sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC q text len p d tb tcap xr v num str k' y' n cap'
  live peak cnt fail cs Qc FP Dk dk HJ HARU HHEADS R1 Rsp Hal0 Hot R8 R20 R10 R11 R12 R3 R4 Hq0 Hq1 HIN Hd3 HTX HTX0
  Hxr HPO HHDR Hncap HBLK HAPART HTMP HG HWF HCS K.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
pose proof HARU as (HAR & _ & _).
assert (HSTK : ESTACK + 144 <= STK_parse_items m)
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items, STK_RT_INTRIN; cbn [fold_right]; lia).
assert (Wv : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; unfold w64; apply wz; exact Hz).
assert (HH : HEAD = 16) by reflexivity.
assert (HE : ESTACK = 4096) by reflexivity.
destruct (fsw_pobj_low B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO) as (Lv1 & Lv2).
assert (Hvimg : pghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v))
  by exact (fsw_pobj_off_img B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Ha & _)|(_ & Ha & _)] _]; exact Ha).
pose proof HHDR as (_ & _ & _ & _ & _ & _ & (Hn0 & _) & (Hc0 & _)).
destruct (pic_blk_facts B lyc Sc W (unpoison Uc memC) mdC memC v k' y' n cap' HAR HPO Hncap ltac:(lia) HBLK HAPART)
  as (EDk & KRB & YRB & KL1 & KL2 & YL1 & YL2 & Kal & Yal & Ki & Yi & Dvk & Dvy & Dky & DkyH).
assert (KinDk : In (k', 56 * cap') Dk) by (unfold Dk; rewrite EDk; left; reflexivity).
assert (YinDk : In (y', 8 * cap') Dk) by (unfold Dk; rewrite EDk; right; left; reflexivity).
pose proof KRB as (KIN & _). pose proof YRB as (YIN & _).
pose proof HTX as (Ht0 & TRB & Htl). pose proof TRB as (TIN & _).
destruct (fsw_rblock_low B lyc Sc W (unpoison Uc memC) mdC memC text tcap HAR TRB) as (T1 & T2).
pose proof HIN as (_ & _ & _ & (Wq0 & Wq1 & Wq2) & Hq8 & _ & _ & Hpp & HL & _ & _ & Hd0).
(* the text block is the entry's, the kids / keys blocks are not: they differ, and their ranges are apart *)
assert (Dkt : pghide (k' + 56 * cap' <= text - HEAD \/ text + tcap <= k' - HEAD)).
{ assert (Hne : (k' - HEAD, 56 * cap' + HEAD) <> (text - HEAD, tcap + HEAD)).
  { intros E. apply (HTMP (k' - HEAD, 56 * cap' + HEAD)); [|rewrite E; exact HTX0].
    unfold Dk, rd_hblocks. rewrite EDk. left. reflexivity. }
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W _ mdC _ _ _ _ HAR KIN TIN Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !FSW_grow_holds.grow_req in D by lia. unfold pghide. lia. }
assert (Dyt : pghide (y' + 8 * cap' <= text - HEAD \/ text + tcap <= y' - HEAD)).
{ assert (Hne : (y' - HEAD, 8 * cap' + HEAD) <> (text - HEAD, tcap + HEAD)).
  { intros E. apply (HTMP (y' - HEAD, 8 * cap' + HEAD)); [|rewrite E; exact HTX0].
    unfold Dk, rd_hblocks. rewrite EDk. right. left. reflexivity. }
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W _ mdC _ _ _ _ HAR YIN TIN Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !FSW_grow_holds.grow_req in D by lia. unfold pghide. lia. }
assert (Hsp0 : alloc_ceiling + ESTACK + 144 <= sp0) by lia.
(* ---- the call of __asan_memset (dk, 0, 56) ---- *)
pose proof (fsw_ecall_preU_at B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own lyc Sc Uc W
  memC mdC kc regsC (sp0 - 144 - ot) HJ HARU ltac:(rewrite Rsp; lia) ltac:(clear - Hal0 Hal16; Z.div_mod_to_equations; lia)
  ltac:(lia) ltac:(lia) ltac:(rewrite R1; unfold YK0s.ret_ok; vm_compute; reflexivity) R3 R4) as HEC.
assert (HDEST : dest_ok tfibsegs B lyc Sc W regsC memC dk 56).
{ intros a Ha. unfold dk in Ha. split; [|split].
  - apply (pic_block_writable B lyc Sc Uc W memC mdC (k' - HEAD) (56 * cap' + HEAD) a HARU KIN).
    rewrite FSW_grow_holds.grow_req by lia. lia.
  - destruct (al_blocks tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC _ _ HAR KIN) as (_ & _ & _ & _ & Hbb & _).
    exact (proj2 (Hbb a ltac:(rewrite FSW_grow_holds.grow_req by lia; lia))).
  - rewrite Rsp. lia. }
assert (HAMR : amem_range dk 56).
{ destruct (al_blocks tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC _ _ HAR KIN) as (_ & _ & _ & Hia & _).
  rewrite FSW_grow_holds.grow_req in Hia by lia.
  assert (HIA : in_app dk 56) by (eapply in_app_sub; [exact Hia | unfold dk; lia | lia | unfold dk; lia]).
  destruct HIA as (H1 & [H2|(H2 & H3)]); unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
    kHighMemEnd, ASAN_CEIL in *; [left; lia | right; lia]. }
assert (HRAD : range_addressable (aview tfibsegs (w_H W) memC) SHADOW_OFF dk 56)
  by exact (fsw_block_body_addressable B lyc Sc Uc W memC mdC (k' - HEAD) (56 * cap' + HEAD) dk 56 HARU HHEADS KIN
    ltac:(unfold dk; lia) ltac:(lia) ltac:(rewrite FSW_grow_holds.grow_req by lia; unfold dk; lia)).
assert (HHULL : shadow_hull_vis (aview tfibsegs (w_H W) memC) dk 56).
{ apply (FSW_pj_parse.pjp_hull_unp B lyc Sc Uc W memC mdC dk 56 HARU ltac:(unfold dk; lia) ltac:(unfold dk; lia) ltac:(lia)).
  apply (shadow_hull_vis_of_block tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC (k' - HEAD) (56 * cap' + HEAD) dk 56
    HAR KIN); [unfold dk; lia | rewrite FSW_grow_holds.grow_req by lia; unfold dk; lia | lia]. }
eapply SRr_bind.
{ eapply (fsw_intrin_atU B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own lyc Sc Uc W memC mdC
    kc Uc (fun a => (dk <= a < dk + 56) \/ (spZ regsC - ESTACK <= a < spZ regsC)) (YK11.getr regsC 1) _
    (fun regs2 mem2 md2 => aregs_preserved regsC regs2 /\ YK11.getr regs2 10 = w64 dk /\
       (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem2 (dk + i) = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (dk <= a < dk + 56) -> ~ (spZ regsC - ESTACK <= a < spZ regsC) ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memC a)) HJ).
  - eapply SRr_mono.
    { exact (MS lyc Sc Uc W regsC memC mdC dk 0 56 HEC R10 R11 R12 ltac:(lia) ltac:(unfold dk; lia)
        ltac:(unfold dk; lia) HDEST HAMR HRAD (fun _ => HHULL) I). }
    cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & Ec & HARU2 & HP & Hsame & H10' & Hset & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split. { rewrite Ec. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    split; [exact HARU2|]. split; [exact Hsame|].
    split.
    { intros a Ha Hn. apply FSW_pj_parse.pjp_aview_unpoison.
      apply Hfr; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H]. }
    split; [intros a; apply FSW_pj_parse.pjp_apresent_unpoison; exact (Hpr a)|].
    split; [exact HP|]. split; [exact H10'|].
    split; [intros i Hi; rewrite (Hset i Hi); reflexivity | exact Hfr].
  - intros a [Ha|Ha].
    + left. right. right. left. exists (k' - HEAD), (56 * cap' + HEAD). split; [exact KIN|]. split.
      * apply HTMP. unfold Dk, rd_hblocks. rewrite EDk. left. reflexivity.
      * rewrite FSW_grow_holds.grow_req by lia. unfold dk in Ha. lia.
    + left. left. rewrite Rsp in Ha. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP & H10' & HZERO & HKEEP).
(* ---- what memset keeps: every byte off the kid and its stack window, raw off the image ---- *)
assert (RAW : forall x, 0 <= x < 2 ^ 64 -> ~ in_img tfibsegs x -> ~ (dk <= x < dk + 56) ->
   ~ (spZ regsC - ESTACK <= x < spZ regsC) ->
   mrestrict (w_H W) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x))
  by (intros x H1 H2 H3 H4; exact (fsw_restrict_of_aview (w_H W) (w_H W) memC mem2 x H1 H2 (HKEEP x H1 H3 H4))).
assert (NIq : forall x, sp0 <= x -> ~ in_img tfibsegs x)
  by (intros x Hx Hi; pose proof (fs_segs_img x Hi); unfold FS_IMG_END in *; lia).
assert (QB : forall x, q <= x < q + 24 -> mrestrict (w_H W) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x))
  by (intros x Hx; apply RAW; [lia | apply NIq; lia | unfold dk; lia | rewrite Rsp; lia]).
assert (VB : forall x, v <= x < v + 56 -> mrestrict (w_H W) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x)).
{ intros x Hx. apply RAW; [lia | exact (pic_noimg B lyc Sc W _ mdC x HAR (pic_pobj_place B lyc Sc W memC v HPO x Hx)) | |].
  - unfold dk, pghide in *. lia.
  - rewrite Rsp. lia. }
assert (BB : forall x, ((k' - HEAD <= x < k' + 56 * cap' /\ ~ (dk <= x < dk + 56)) \/ y' - HEAD <= x < y' + 8 * cap' \/
     text - HEAD <= x < text + tcap) ->
   mrestrict (w_H W) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x)).
{ intros x Hx. apply RAW; [lia | | | rewrite Rsp; lia].
  - destruct Hx as [(Hx & _)|[Hx|Hx]].
    + apply (blk_img tfibsegs B LAWS lyc Sc W _ mdC _ _ x HAR KIN). rewrite FSW_grow_holds.grow_req by lia. lia.
    + apply (blk_img tfibsegs B LAWS lyc Sc W _ mdC _ _ x HAR YIN). rewrite FSW_grow_holds.grow_req by lia. lia.
    + apply (blk_img tfibsegs B LAWS lyc Sc W _ mdC _ _ x HAR TIN). rewrite FSW_grow_holds.grow_req by lia. lia.
  - destruct Hx as [(Hx & Hn)|[Hx|Hx]]; [exact Hn | pose proof DkyH as D | pose proof Dkt as D]; unfold pghide, dk in *;
      clear - D Hx Hncap Hn0 HH; lia. }
assert (MBq : forall x, q <= x < q + 24 \/ v <= x < v + 56 ->
   mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) memC) x)
  by (intros x [Hx|Hx]; unfold mbyte; [rewrite (QB x Hx) | rewrite (VB x Hx)]; reflexivity).
(* ---- the facts at the resume ---- *)
assert (HIN2 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem2) q text len p d tb).
{ apply (FSW_parse_string.pc_pj_in_ok_keep (mrestrict (w_H W) memC) _ q text len p d tb HIN).
  - intros i Hi. apply MBq. left. lia.
  - intros i Hi. apply (pic_writable_eq (mrestrict (w_H W) memC)); [exact (QB (q + i) ltac:(lia)) | exact (Wq2 i Hi)].
  - intros i Hi. unfold mbyte. rewrite (BB (text + i)); [reflexivity|]. right; right. lia. }
assert (HHDR2 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem2) v 6 num str k' y' n cap').
{ apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) memC)); [exact HHDR|].
  intros x Hx. exact (FSW_grow_holds.grow_word_eq _ _ (fun z => v <= z < v + 56) x VB Hx). }
assert (SHk : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memC a).
{ intros a Ha. apply HKEEP; [unfold SHADOW_OFF in *; lia | | rewrite Rsp; unfold SHADOW_OFF in *; lia].
  intros Hk. apply (fsw_ablock_off_shadow B lyc Sc W (unpoison Uc memC) mdC _ _ HAR KIN a); [|exact Ha].
  rewrite FSW_grow_holds.grow_req by lia. unfold dk in Hk. lia. }
assert (HPO2 : pobj tfibsegs B lyc Sc W mem2 v)
  by (apply (pic_pobj_keep B lyc Sc W memC mem2 v HPO); [intros i Hi; exact (VB (v + i) ltac:(lia)) | exact SHk | lia | lia]).
assert (BLK2 : rd_blocks_ok tfibsegs B lyc Sc W mem2 Dk).
{ intros a0 k0 Hak. unfold Dk in Hak. rewrite EDk in Hak. destruct Hak as [Eq|[Eq|[]]]; injection Eq as <- <-.
  - apply (pic_rblock_keep_raw B lyc Sc W memC mem2 k' _ KRB). intros x Hx. apply BB. left. unfold dk. lia.
  - apply (pic_rblock_keep_raw B lyc Sc W memC mem2 y' _ YRB). intros x Hx. apply BB. right; left. lia. }
assert (HTX2 : rd_text tfibsegs B lyc Sc W mem2 text len tcap).
{ split; [exact Ht0|]. split; [|exact Htl].
  apply (pic_rblock_keep_raw B lyc Sc W memC mem2 text _ TRB). intros x Hx. apply BB. right; right. lia. }
assert (HG2 : fs_glob tfibsegs W mem2 live peak cnt fail).
{ apply (FSW_pj_parse.pjp_glob_keep W memC mem2 live peak cnt fail); [|exact HG].
  intros x Hx. pose proof (pic_img_lo x Hx). apply HKEEP; [unfold FS_IMG_END in *; lia | unfold dk, pghide in *; lia |].
  rewrite Rsp. unfold FS_IMG_END in *. lia. }
assert (ZB : forall i, 0 <= i < 56 -> mbyte tfibsegs (mrestrict (w_H W) mem2) (dk + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. pose proof (HZERO i Hi) as Hz. unfold aview in Hz.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (dk + i)) as [b|] eqn:Eb; [|discriminate].
  cbn in Hz. injection Hz as Hz. f_equal. apply bv_eq. rewrite Hz. reflexivity. }
assert (KW2 : forall x, dk <= x < dk + 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) x).
{ intros x Hx. apply (pic_block_writable B lyc Sc Uc W mem2 md2 (k' - HEAD) (56 * cap' + HEAD) x HARU2 KIN).
  rewrite FSW_grow_holds.grow_req by lia. unfold dk in Hx. lia. }
assert (Hdk8 : dk mod 8 = 0) by (unfold dk; clear - Kal; Z.div_mod_to_equations; lia).
assert (HZ2 : PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem2) dk).
{ split; [split; [exact Hdk8|]|].
  - split; [unfold dk; lia|]. split; [unfold dk; lia|]. intros a Ha. split; [exact (KW2 a Ha)|].
    exists (Z_to_bv 8 0). rewrite FSW_parse_string.pstr_mrd_mbyte. replace a with (dk + (a - dk)) by lia. apply ZB. lia.
  - split; [unfold dk; lia|]. rewrite repeat_length. split; [unfold dk; lia|]. intros i Hi.
    rewrite FSW_parse_string.pstr_mrd_mbyte, nth_error_repeat by exact Hi. apply ZB. lia. }
assert (HPK2 : pobj tfibsegs B lyc Sc W mem2 dk).
{ split.
  - right. split; [exists (k' - HEAD), (56 * cap' + HEAD); split; [exact KIN | rewrite FSW_grow_holds.grow_req by lia; unfold dk; lia]|].
    split; [exact Hdk8|].
    exact (fsw_block_body_addressable B lyc Sc Uc W mem2 md2 (k' - HEAD) (56 * cap' + HEAD) dk 56 HARU2 HHEADS KIN
      ltac:(unfold dk; lia) ltac:(lia) ltac:(rewrite FSW_grow_holds.grow_req by lia; unfold dk; lia)).
  - intros i Hi. apply KW2. lia. }
(* ---- the resume env ---- *)
set (xs := pig_xs p (text + len) d xr k' y' n cap').
set (E := Ereg regs2 (fs_extraT ++ xs)).
assert (G8 : YK11.getr regs2 8 = w64 q) by (rewrite <- R8; exact (HP 8 ltac:(unfold acallee_saved; lia))).
assert (G20 : YK11.getr regs2 20 = w64 v) by (rewrite <- R20; exact (HP 20 ltac:(unfold acallee_saved; lia))).
assert (G2 : YK11.getr regs2 2 = YK11.getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp2 : spZ regs2 = sp0 - 144) by (unfold spZ; rewrite G2; exact Rsp).
assert (E8 : bv_unsigned (ew E 8) = q) by (unfold E; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G8; apply Wv; lia).
assert (E20 : bv_unsigned (ew E 20) = v) by (unfold E; rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl), G20; apply Wv; lia).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 144) by (unfold E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Usp2).
destruct (pig_xs_nth p (text + len) d xr k' y' n cap' Hxr) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
assert (XA : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
assert (Y0 : ew E (xatom 0) = Z_to_bv 64 p) by (rewrite XA; exact X0).
assert (Y1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite XA; exact X1).
assert (Y2 : ew E (xatom 2) = Z_to_bv 64 d) by (rewrite XA; exact X2).
assert (Y16 : ew E (xatom 16) = Z_to_bv 64 k') by (rewrite XA; exact X16).
assert (Y17 : ew E (xatom 17) = Z_to_bv 64 y') by (rewrite XA; exact X17).
assert (Y18 : ew E (xatom 18) = Z_to_bv 64 n) by (rewrite XA; exact X18).
assert (Y19 : ew E (xatom 19) = Z_to_bv 64 cap') by (rewrite XA; exact X19).
assert (VW2 : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + i)) by exact (proj2 HPO2).
assert (HRSOK : Forall (region_ok tfibsegs E (mrestrict (w_H W) mem2)) (pic_rs cap')).
{ unfold pic_rs.
  constructor; [exact (pic_q_ok E _ q text len p d tb E8 Y0 Y1 Y2 HIN2)|].
  constructor; [exact (pic_v_ok E _ v num str k' y' n cap' E20 Y16 Y17 Y18 Y19 ltac:(lia) ltac:(lia) VW2 HHDR2)|].
  constructor.
  { apply (pic_blk_ok E _ (xatom 16) k'); [rewrite Y16; apply wz; lia | lia | lia |]. intros i Hi.
    apply (pic_block_writable B lyc Sc Uc W mem2 md2 (k' - HEAD) (56 * cap' + HEAD)); [exact HARU2 | exact KIN|].
    rewrite FSW_grow_holds.grow_req by lia. lia. }
  constructor; [|constructor].
  apply (pic_blk_ok E _ (xatom 17) y'); [rewrite Y17; apply wz; lia | lia | lia |]. intros i Hi.
  apply (pic_block_writable B lyc Sc Uc W mem2 md2 (y' - HEAD) (8 * cap' + HEAD)); [exact HARU2 | exact YIN|].
  rewrite FSW_grow_holds.grow_req by lia. lia. }
assert (HPD : pairwise_disjoint E (fsT_ret_regions 144 cs (pic_rs cap'))).
{ apply (pic_disj E cs cap' (sp0 - 144) q v k' y' E2 E8 E20); try assumption;
    [rewrite Y16; apply wz; lia | rewrite Y17; apply wz; lia | ..]; lia. }
assert (HGF : atoms_ok E pic_gf).
{ apply (pic_gf_ok E q v p (text + len) d k' y' n cap' E8 E20 Y0 Y1 Y2 Y16 Y17 Y18 Y19);
    first [exact Hq8 | exact Hv8 | exact Kal | exact Yal | lia]. }
assert (HKF : forall x, sp0 - 144 <= x < sp0 ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) memC) x).
{ intros x Hx. apply (mbyte_of_aview tfibsegs). apply HKEEP; [lia | unfold dk; lia | rewrite Rsp; lia]. }
pose proof (pic_resumeT B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own lyc Sc Uc W mem2 md2
  kc regs2 sp0 144 xs cs (pic_rs cap') pic_gf 0x84d7c (mrestrict (w_H W) memC)
  (proj1 HSS) (proj2 HSS) HJ2 HARU2 Usp2 ltac:(lia) ltac:(clear - Hal0; Z.div_mod_to_equations; lia) ltac:(lia) Hot
  (pic_wf cs cap' ltac:(lia) HWF) (HCS regs2 HP) HKF HRSOK HPD HGF) as HST.
rewrite R1.
exact (K regs2 mem2 md2 HJ2 HARU2 HP H10' HST HKEEP HZ2 HPK2 HIN2 HHDR2 HPO2 MBq BLK2 HTX2 HG2).
Qed.
End ms.

(* ================= parse_items' parse_value call at level k + 1 (0x84d98 -> 0x84d9c) ================= *)
Section pv. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Variable k : nat.
(* callee: parse_value at level k + 1 *)
Hypothesis HPV : @parse_value_spec fx rc SK tfibsegs B (S k).
(* the callee's level, named once (the state binder S of the statements below shadows the constructor) *)
Let k1 : nat := S k.

(* the call at ra 0x84d9c: a0 = s0 = q, a1 = vk = kids' + 56 * n (the kid, zeroed by the memset step), in->depth =
   k + 1. parse_items OWES parse_value's left frame-chain arm: s0Z regsC = q (from the premise on register 8) and the
   chain chq at q on the call memory with every NEXT
   pointer a stop or >= q + 40 (parse_items' own premise, carried to the call). Premises beyond grow's: the text
   block's request at the entry (the kids block is temporary, so the two differ), the frames bound at level k + 1,
   parse_value's own (the bytes at in->p, FS_DOC_STRS, the kid's pobj and zeroes, the budgets), tmp, n < cap'. *)
Definition pic_pv_at : Prop :=
  forall sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC chq q text len p (tb : list byte) tcap
    xr v num str k' y' n cap' (u : PjTree.jv) (pr : bool) (ws rest : list Z) live peak cnt fail cs
    (Qc : world tfibsegs -> config -> Prop),
  let FP := [(v, v + 56)] ++ FS_PSTAT_FP in
  let Dk := ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap' in
  let vk := k' + 56 * n in
  let tr := PjRoundTrip.ttrace u in
  let wt := concat (WriterValue.wvpieces u pr (Z.of_nat k1)) in
  let p' := p + Z.of_nat (length ws) + Z.of_nat (length wt) in
  (k <= 1)%nat ->
  ajournal tfibsegs B (STK_parse_items (1 - k) + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    lyc Sc W (unpoison Uc memC) mdC kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B lyc Sc Uc -> Z.of_nat (length (frames Sc)) <= FRL_parse_value (Z.of_nat k1) ->
  YK11.getr regsC 1 = w64 0x84d9c -> spZ regsC = sp0 - 144 -> sp0 mod 16 = 0 -> sp0 <= ot ->
  YK11.getr regsC 8 = w64 q -> YK11.getr regsC 20 = w64 v ->
  YK11.getr regsC 10 = w64 q -> YK11.getr regsC 11 = w64 vk ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison Uc memC)) (spZ regsC) q chq ->
  Forall (fun r => bad_next (fst (fst r)) (ly_top lyc) (snd r) = true \/ q + 40 <= snd r) chq ->
  sp0 <= q -> q + 24 <= ot ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p (Z.of_nat k1) tb ->
  rd_text tfibsegs B lyc Sc W memC text len tcap -> In (text - HEAD, tcap + HEAD) (ablocks B ly S) ->
  ReaderRes.rest_at tb text p = ws ++ wt ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  (forall x, In x (u :: FSDocStrs.jv_vals u) -> FSDocStrs.str_or_obj x) -> FSDocStrs.fs_doc_strings u ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod u -> (PjTree.depth u <= 2 - k1)%nat ->
  length xr = 13%nat ->
  pobj tfibsegs B lyc Sc W memC v -> PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) memC) v 6 num str k' y' n cap' ->
  n < cap' -> rd_blocks_ok tfibsegs B lyc Sc W memC Dk -> PjStruct.pj_apart Dk v ->
  (forall b, In b (rd_hblocks Dk) -> ~ In b (ablocks B ly S)) ->
  pobj tfibsegs B lyc Sc W memC vk -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) memC) vk ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev Sc + rd_ev tr <= EV_MAX -> blocks_bytes Sc + rd_live tr <= LIVE_MAX ->
  regions_wf [fstk_ret 144 cs] = true ->
  (forall regs', aregs_preserved regsC regs' ->
     Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ pig_xs p' (text + len) (Z.of_nat k1) xr k' y' n cap'))
       (mrestrict (w_H W) memC) (sp0 - 144)) cs) ->
  (forall D Da ly' S' W' regs' mem' md',
     Permutation Da D ->
     ajournal tfibsegs B (STK_parse_items (1 - k) + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
       ly' S' W' (unpoison (Uc ++ rd_heads Da) mem') md' (kc + rd_ev tr) ->
     ajournal tfibsegs B (STK_parse_value (2 - k1) + (ot - spZ regsC)) ot ([(vk, vk + 56)] ++ FS_PSTAT_FP)
       lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison (Uc ++ rd_heads Da) mem') md' (rd_ev tr) ->
     ARU tfibsegs B ly' S' (Uc ++ rd_heads Da) W' mem' md' ->
     aregs_preserved regsC regs' -> YK11.getr regs' 10 = w64 0 ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pig_xs p' (text + len) (Z.of_nat k1) xr k' y' n cap'))
       (fss_retT 0x84d9c 144 cs (pic_rs cap') pic_gf)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84d9c) mem' (seg_rom tfibsegs))) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len p' (Z.of_nat k1) tb ->
     wkeep tfibsegs W W' memC mem' (spZ regsC) ot q 24 ->
     Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ rd_hblocks D) ->
     rtree tfibsegs B ly' S' W' mem' vk u D -> rd_sum D = PjGrammar.held tr -> (length D <= length tr)%nat ->
     pobj tfibsegs B ly' S' W' mem' vk -> rd_text tfibsegs B ly' S' W' mem' text len tcap ->
     (exists peak', peak <= peak' /\
        fs_glob tfibsegs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail) ->
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 num str k' y' n cap' ->
     (forall x, v <= x < v + 56 -> mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x) ->
     rd_blocks_ok tfibsegs B ly' S' W' mem' Dk ->
     (forall x, k' <= x < k' + 56 * cap' \/ y' <= x < y' + 8 * cap' -> ~ (vk <= x < vk + 56) ->
        mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x84d9c) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_value regsC memC mdC) Qc.

Lemma pic_call_pv_84d98 : pic_pv_at.
Proof.
intros sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC chq q text len p tb tcap xr v num str k' y' n cap'
  u pr ws rest live peak cnt fail cs Qc FP Dk vk tr wt p' Hk HJ HARU HRO HHEADS HFRL R1 Rsp Hal0 Hot R8 R20 R10 R11 R3 R4
  HCH HFW Hq0 Hq1 HIN HTX HTX0 HREST HWS HSO HSTR HWF HDEP Hxr HPO HHDR Hncap HBLK HAPART HTMP HPK HZK HG HQ HSZ HLIVE
  HEV HLV HWFr HCS K.
change (2 - k1)%nat with (1 - k)%nat in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HARU as (HAR & _ & _).
assert (HSTK : STK_parse_value (1 - k) + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
assert (HSTK0 : 0 <= STK_parse_value (1 - k))
  by (destruct (1 - k)%nat; cbn [STK_parse_value]; unfold PROBE_parse_value, PROBE_PAGE; lia).
assert (Wv : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; unfold w64; apply wz; exact Hz).
assert (HH : HEAD = 16) by reflexivity.
destruct (fsw_pobj_low B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO) as (Lv1 & Lv2).
assert (Hvimg : pghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v))
  by exact (fsw_pobj_off_img B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Ha & _)|(_ & Ha & _)] _]; exact Ha).
pose proof HHDR as (_ & _ & _ & _ & _ & _ & (Hn0 & _) & (Hc0 & _)).
destruct (pic_blk_facts B lyc Sc W (unpoison Uc memC) mdC memC v k' y' n cap' HAR HPO Hncap ltac:(lia) HBLK HAPART)
  as (EDk & KRB & YRB & KL1 & KL2 & YL1 & YL2 & Kal & Yal & Ki & Yi & Dvk & Dvy & Dky & DkyH).
assert (KinDk : In (k', 56 * cap') Dk) by (unfold Dk; rewrite EDk; left; reflexivity).
assert (YinDk : In (y', 8 * cap') Dk) by (unfold Dk; rewrite EDk; right; left; reflexivity).
pose proof KRB as (KIN & _). pose proof YRB as (YIN & _).
pose proof HTX as (Ht0 & TRB & Htl). pose proof TRB as (TIN & _).
destruct (fsw_rblock_low B lyc Sc W (unpoison Uc memC) mdC memC text tcap HAR TRB) as (T1 & T2).
pose proof HIN as (_ & _ & _ & _ & Hq8 & _ & _ & Hpp & _ & _ & _ & Hd0).
assert (Dkt : pghide (k' + 56 * cap' <= text - HEAD \/ text + tcap <= k' - HEAD)).
{ assert (Hne : (k' - HEAD, 56 * cap' + HEAD) <> (text - HEAD, tcap + HEAD)).
  { intros E. apply (HTMP (k' - HEAD, 56 * cap' + HEAD)); [|rewrite E; exact HTX0].
    unfold Dk, rd_hblocks. rewrite EDk. left. reflexivity. }
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W _ mdC _ _ _ _ HAR KIN TIN Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !FSW_grow_holds.grow_req in D by lia. unfold pghide. lia. }
assert (Hsp0 : alloc_ceiling + STK_parse_value (1 - k) + 144 <= sp0) by lia.
(* ---- parse_value's fpreU and window at the call ---- *)
assert (PRE : fpreU tfibsegs B (STK_parse_value (1 - k)) lyc Sc Uc W regsC memC mdC chq).
{ apply (fsw_fpreU_atFP B (STK_parse_items (1 - k) + (ot - sp0)) ot FP ly S Uc W0 (unpoison U0 mem0) md0 own lyc Sc W memC
    mdC kc regsC (STK_parse_value (1 - k)) (sp0 - 144 - ot) chq HJ HARU HRO).
  - rewrite Rsp. lia.
  - clear - Hal0 Hal16. Z.div_mod_to_equations. lia.
  - lia.
  - exact HSTK0.
  - lia.
  - rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
  - unfold raZ. rewrite R1, Wv by lia. lia.
  - exact R3.
  - exact R4.
  - unfold s0Z. rewrite R8, Wv by lia. exact HCH. }
assert (HWIN : rd_win tfibsegs regsC lyc W memC q ot).
{ unfold rd_win. rewrite Rsp. split; [lia|]. split; [lia|]. split; [exact Hal16|]. split; [rewrite Etop; exact Htop|].
  intros a0 Ha0. apply (fsw_apresent_unpoison B lyc Sc Uc W memC mdC a0 HARU); [lia|]. apply Hpres. lia. }
(* ---- the call ---- *)
eapply SRr_bind.
{ apply (HPV lyc Sc Uc W regsC memC mdC chq q ot vk text len p tb tcap u pr ws rest live peak cnt fail).
  - lia.
  - exact PRE.
  - exact HHEADS.
  - exact HFRL.
  - exact R10.
  - exact R11.
  - exact HIN.
  - exact HWIN.
  - right. split; [rewrite Rsp; lia|]. split; [unfold s0Z; rewrite R8, Wv by lia; reflexivity|].
    exists chq. split; [exact HCH | exact HFW].
  - exact HTX.
  - exact HREST.
  - exact HWS.
  - exact HSO.
  - exact HSTR.
  - exact HWF.
  - exact HDEP.
  - exact HPK.
  - exact HZK.
  - left. rewrite Rsp. unfold vk. change (Nat.sub 2 (Datatypes.S k)) with (Nat.sub 1 k). lia.
  - unfold vk, pghide in *. clear - Dkt Hncap Hn0 HH. lia.
  - exact HG.
  - exact HQ.
  - exact HSZ.
  - exact HLIVE.
  - exact HEV.
  - exact HLV. }
intros W' c' _ (D & Da & HPm & ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP &
  (A0 & HIN' & HWK & HPERM & HRT & HSUM & HLEN & HPOk' & HTX' & HG')).
(* ---- the composed journal ---- *)
set (FP1 := [(vk, vk + 56)] ++ FS_PSTAT_FP) in *.
assert (HFPS : fsw_fp_sub B ly S lyc Sc own FP FP1).
{ intros a0 Ha0. unfold FP1 in Ha0. apply inFP_app in Ha0 as [Ha0|Ha0].
  - right; left. apply inFP_cons in Ha0 as [Ha0|Ha0]; [|destruct (inFP_nil _ Ha0)].
    exists (k' - HEAD), (56 * cap' + HEAD). split; [exact KIN|].
    split; [apply HTMP; unfold Dk, rd_hblocks; rewrite EDk; left; reflexivity|].
    rewrite FSW_grow_holds.grow_req by lia. unfold vk in Ha0. lia.
  - right; right; left. split; [unfold FP; apply inFP_app; right; exact Ha0 | exact (pig_pstat_img a0 Ha0)]. }
set (U' := Uc ++ rd_heads Da) in *.
assert (I1 : ot - (STK_parse_items (1 - k) + (ot - sp0)) <= ot - (STK_parse_value (1 - k) + (ot - spZ regsC)))
  by (rewrite Rsp; lia).
assert (HJ2 : ajournal tfibsegs B (STK_parse_items (1 - k) + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    ly' S' W' (unpoison U' mem') md' (kc + rd_ev tr))
  by exact (fsw_ajournal_sub5 B _ ot FP ly S W0 (unpoison U0 mem0) md0 own lyc Sc W (unpoison Uc memC) mdC kc
              _ ot FP1 [] ly' S' W' (unpoison U' mem') md' _ HJ HJc I1 (Z.le_refl ot) HFPS).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
pose proof HJc as (HARc' & _).
(* ---- what parse_value keeps: every block / frame byte of the call off the kid ---- *)
assert (NFP : forall x, ~ in_img tfibsegs x -> ~ (vk <= x < vk + 56) -> ~ inFP FP1 x).
{ intros x Hx Hn Hf. unfold FP1 in Hf. apply inFP_app in Hf as [Hf|Hf].
  - apply inFP_cons in Hf as [Hf|Hf]; [exact (Hn Hf) | exact (inFP_nil _ Hf)].
  - exact (Hx (pig_pstat_img x Hf)). }
assert (KB : forall x, ((exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= x < p0 + req_size n0) \/
      (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
   ~ (vk <= x < vk + 56) ->
   mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x)).
{ intros x Hx Hn. refine (proj2 (fsw_journal_kept_byte B _ _ _ lyc Sc Uc W memC mdC ly' S' U' W' mem' md' _ x HJc HARU OK' PO'
    Hx _)).
  exact (NFP x (pic_noimg B lyc Sc W (unpoison Uc memC) mdC x HAR Hx) Hn). }
assert (VB : forall x, v <= x < v + 56 -> mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W) memC (Z_to_bv 64 x)).
{ intros x Hx. apply KB; [exact (pic_pobj_place B lyc Sc W memC v HPO x Hx)|].
  unfold vk, pghide in *. clear - Dvk Hx Hncap Hn0. lia. }
assert (VBm : forall x, v <= x < v + 56 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x)
  by (intros x Hx; unfold mbyte; rewrite (VB x Hx); reflexivity).
assert (HHDR' : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 num str k' y' n cap').
{ apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) memC)); [exact HHDR|].
  intros x Hx. exact (FSW_grow_holds.grow_word_eq _ _ (fun z => v <= z < v + 56) x VB Hx). }
assert (VW' : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i)).
{ intros i Hi. apply (pic_writable_eq (mrestrict (w_H W) memC)); [exact (VB (v + i) ltac:(lia)) | exact (proj2 HPO i Hi)]. }
assert (BLK' : rd_blocks_ok tfibsegs B ly' S' W' mem' Dk).
{ intros a0 k0 Hak. unfold Dk in Hak. rewrite EDk in Hak. destruct Hak as [Eq|[Eq|[]]]; injection Eq as <- <-.
  - apply (pic_rblock_kept B _ _ _ lyc Sc Uc W memC mdC ly' S' U' W' mem' md' _ k' _ HJc HARU OK' PO'); [|exact KRB].
    intros x Hx. apply NFP; [|unfold vk; lia].
    apply (blk_img tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC _ _ x HAR KIN).
    rewrite FSW_grow_holds.grow_req by lia. lia.
  - apply (pic_rblock_kept B _ _ _ lyc Sc Uc W memC mdC ly' S' U' W' mem' md' _ y' _ HJc HARU OK' PO'); [|exact YRB].
    intros x Hx. apply NFP; [|unfold vk, pghide in *; clear - DkyH Hx Hncap Hn0 HH; lia].
    apply (blk_img tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC _ _ x HAR YIN).
    rewrite FSW_grow_holds.grow_req by lia. lia. }
assert (KBm : forall x, k' <= x < k' + 56 * cap' \/ y' <= x < y' + 8 * cap' -> ~ (vk <= x < vk + 56) ->
   mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x).
{ intros x Hx Hn. unfold mbyte. rewrite KB; [reflexivity | | exact Hn]. left.
  destruct Hx as [Hx|Hx]; [exists (k' - HEAD), (56 * cap' + HEAD) | exists (y' - HEAD), (8 * cap' + HEAD)].
  - split; [exact KIN | rewrite FSW_grow_holds.grow_req by lia; lia].
  - split; [exact YIN | rewrite FSW_grow_holds.grow_req by lia; lia]. }
pose proof (proj1 (BLK' k' (56 * cap') KinDk)) as KIN'. pose proof (proj1 (BLK' y' (8 * cap') YinDk)) as YIN'.
(* ---- the resume env ---- *)
set (xs := pig_xs p' (text + len) (Z.of_nat k1) xr k' y' n cap').
set (E := Ereg regs' (fs_extraT ++ xs)).
assert (G8 : YK11.getr regs' 8 = w64 q) by (rewrite <- R8; exact (HP 8 ltac:(unfold acallee_saved; lia))).
assert (G20 : YK11.getr regs' 20 = w64 v) by (rewrite <- R20; exact (HP 20 ltac:(unfold acallee_saved; lia))).
assert (G2 : YK11.getr regs' 2 = YK11.getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp' : spZ regs' = sp0 - 144) by (unfold spZ; rewrite G2; exact Rsp).
assert (E8 : bv_unsigned (ew E 8) = q) by (unfold E; rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), G8; apply Wv; lia).
assert (E20 : bv_unsigned (ew E 20) = v) by (unfold E; rewrite (ew_Ereg_nat regs' _ 20 20%bv eq_refl), G20; apply Wv; lia).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 144) by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Usp').
destruct (pig_xs_nth p' (text + len) (Z.of_nat k1) xr k' y' n cap' Hxr) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
assert (XA : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
assert (Y0 : ew E (xatom 0) = Z_to_bv 64 p') by (rewrite XA; exact X0).
assert (Y1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite XA; exact X1).
assert (Y2 : ew E (xatom 2) = Z_to_bv 64 (Z.of_nat k1)) by (rewrite XA; exact X2).
assert (Y16 : ew E (xatom 16) = Z_to_bv 64 k') by (rewrite XA; exact X16).
assert (Y17 : ew E (xatom 17) = Z_to_bv 64 y') by (rewrite XA; exact X17).
assert (Y18 : ew E (xatom 18) = Z_to_bv 64 n) by (rewrite XA; exact X18).
assert (Y19 : ew E (xatom 19) = Z_to_bv 64 cap') by (rewrite XA; exact X19).
pose proof HIN' as (_ & _ & _ & _ & _ & _ & _ & HPp & _).
assert (HRSOK : Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) (pic_rs cap')).
{ unfold pic_rs.
  constructor; [exact (pic_q_ok E _ q text len p' (Z.of_nat k1) tb E8 Y0 Y1 Y2 HIN')|].
  constructor; [exact (pic_v_ok E _ v num str k' y' n cap' E20 Y16 Y17 Y18 Y19 ltac:(lia) ltac:(lia) VW' HHDR')|].
  constructor.
  { apply (pic_blk_ok E _ (xatom 16) k'); [rewrite Y16; apply wz; lia | lia | lia |]. intros i Hi.
    apply (pic_block_writable B ly' S' U' W' mem' md' (k' - HEAD) (56 * cap' + HEAD)); [exact HARU' | exact KIN'|].
    rewrite FSW_grow_holds.grow_req by lia. lia. }
  constructor; [|constructor].
  apply (pic_blk_ok E _ (xatom 17) y'); [rewrite Y17; apply wz; lia | lia | lia |]. intros i Hi.
  apply (pic_block_writable B ly' S' U' W' mem' md' (y' - HEAD) (8 * cap' + HEAD)); [exact HARU' | exact YIN'|].
  rewrite FSW_grow_holds.grow_req by lia. lia. }
assert (HPD : pairwise_disjoint E (fsT_ret_regions 144 cs (pic_rs cap'))).
{ apply (pic_disj E cs cap' (sp0 - 144) q v k' y' E2 E8 E20); try assumption;
    [rewrite Y16; apply wz; lia | rewrite Y17; apply wz; lia | ..]; lia. }
assert (HGF : atoms_ok E pic_gf).
{ apply (pic_gf_ok E q v p' (text + len) (Z.of_nat k1) k' y' n cap' E8 E20 Y0 Y1 Y2 Y16 Y17 Y18 Y19);
    first [exact Hq8 | exact Hv8 | exact Kal | exact Yal | lia | unfold k1; lia | unfold p', wt, k1 in *; lia]. }
(* ---- the resume ---- *)
assert (HKEEP : forall x, sp0 - 144 <= x < sp0 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x)
  by (intros x Hx; exact (proj1 (HWK x ltac:(rewrite Rsp; lia) ltac:(lia)))).
pose proof (pic_resumeT B (STK_parse_items (1 - k) + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own ly' S' U' W'
  mem' md' (kc + rd_ev tr) regs' sp0 144 xs cs (pic_rs cap') pic_gf 0x84d9c (mrestrict (w_H W) memC)
  (proj1 HSS) (proj2 HSS) HJ2 HARU' Usp' ltac:(lia) ltac:(clear - Hal0; Z.div_mod_to_equations; lia) ltac:(lia) Hot
  (pic_wf cs cap' ltac:(lia) HWFr) (HCS regs' HP) HKEEP HRSOK HPD HGF) as HST.
rewrite R1.
exact (K D Da ly' S' W' regs' mem' md' HPm HJ2 HJc HARU' HP A0 HST HIN' HWK HPERM HRT HSUM HLEN HPOk' HTX' HG' HHDR'
  VBm BLK' KBm).
Qed.
End pv.
