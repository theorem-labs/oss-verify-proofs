(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 1494 of its 1575 lines of code are new or changed and 1058 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_op4r.v, with its module paths and module names changed; 698 of its 806 lines of code are new or changed and 1467 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_st: the state bridges of the image-B walk of LLVMFuzzerTestOneInput (the cuts of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), proved:
   1. the cut states' constant parts: the frame shadow maps (lf_shm) and the spill slots (lf_spill_loop), their
      offsets and byte ranges;
   2. the shadow facts of the read-only ranges the walk hands a callee: trans_sh_any of the 13 ranges from the record
      facts transport_cells and trans_llvmf_cells alone, over one closed cover list (the cover kit of section 2a:
      image A's lib/A/Prog/DgnTransportCgX.v trans_sh_cells / trans_cs_cover / trans_sh_any_cells, read at image B's
      lib/B/Prog/DgnTransportBCg.v trans_sh_any, decode_zshadow_at and AsanCells); and lc_rom_bytes, the read-only
      bytes the walk reads, as the image holds them;
   3. the model bridges: each model piece the cuts name (segs.v section 1) is TOps.v's or TCb.v's own text, by a lemma
      that rewrites LLVMFuzzerTestOneInput_m (lc_pro_eq), LLVMFuzzerTestOneInput_op_m per op code (lc_recv_eq,
      lc_frame_eq, lc_ann_eq, lc_tick_eq, lc_op4_eq, lc_submit_raw_eq, lc_submit_tag_eq, lc_op5_eq, lc_op6_eq,
      lc_op7_eq), the raw length word (lc_raw_vals_eq) and m_close up to its call of m_set (lc_close_eq); each is
      proved by unfolding and destructing the cursor reads, with no computation on a world; lc_settle_world (settle
      keeps the world it is given);
   4. the simulation step at the loop tail (lc_tail_agree): the operation's model equation at a stream fun _ => a with
      recv_addr_ok a gives agree timg_B (ops + 1) at its world (LoopOk.v op_ok, op_k_of; LinksProof.v links_holds);
   5. the list of the error exits (__asan_report_*, the abort pair and the 74 branches to the UBSan trap word) with the
      segment that rules each out;
   6. the geometry of the core and its transfer: lc_geom; lc_core_kept_run, the transfer over a stretch (a run, a call
      or both) that asks only what lc_core reads (the journal at the new state, frames, blocks, sp / gp / tp / s0 /
      s1, the 13 saved words, the input's bytes, the frame's last word and the presence of the frame's bytes), so a
      stretch may write the rest of the frame, its shadow, the spill slots and the other registers; lc_core_kept, its
      form for a call (aregs_preserved, every byte from alloc_ceiling up outside the window below sp1); and the two
      bridges of the journal at FP = [] that EXIT reads: lc_fp_token widens it to the
      post's FP = [sink_token], lc_journal_io gives the file descriptors and the file system. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_init_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts InitOk LoopOk LinksProof.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.

(* ------------------------------------------------------------------ *)
(* 1. The constant parts of the cuts                                    *)
(* ------------------------------------------------------------------ *)

(* Every shadow value of the frame maps is a byte. *)
Lemma lf_shm_byte : forall cin bin i, (i < 32)%nat -> 0 <= nth i (lf_shm cin bin) 0 < 256.
Proof.
intros cin bin i Hi.
do 32 (destruct i as [|i]; [destruct cin, bin; cbn; lia|]). lia.
Qed.

(* The spill slots: their offsets (each 8-aligned, inside [32, 192), pairwise distinct, below the saved words at
   sp0 - 104 >= sp1 + 216) and their values (each a word). *)
Lemma lf_spill_offsets : forall F,
  map fst (lf_spill_loop F) = [128; 136; 104; 152; 184; 40; 168; 32; 56; 112; 88; 120; 48; 160; 72; 96; 80; 176; 144].
Proof. intros F. reflexivity. Qed.
Lemma lf_spill_nodup : forall F, List.NoDup (map fst (lf_spill_loop F)).
Proof.
intros F. rewrite lf_spill_offsets.
repeat (apply List.NoDup_cons; [intro Hin; cbn in Hin; repeat (destruct Hin as [Hin|Hin]; [lia|]); exact Hin|]).
apply List.NoDup_nil.
Qed.
Lemma lf_spill_vals : forall F, 0 <= F -> F + LF_FBYTES <= 2 ^ 63 ->
  Forall (fun o : Z * Z => 0 <= snd o < 2 ^ 64 /\ fst o mod 8 = 0 /\ 8 <= fst o /\ fst o + 8 <= 192) (lf_spill_loop F).
Proof.
intros F H0 H1. unfold LF_FBYTES in H1.
destruct lf_spill_pages as (E8 & E9 & E10 & E11 & E14 & E15).
unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. rewrite E8, E9, E10, E11, E14, E15.
unfold TB_M, TB_g_s. change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 63) with 9223372036854775808 in *.
repeat constructor; cbn [fst snd]; try lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The shadow facts of the read-only ranges and the image bytes     *)
(* ------------------------------------------------------------------ *)

(* 2a. The cover kit at image B: trans_sh_any from the record's shadow cells, for a range whose 64-byte hull holds
   constant shadow bytes that are not 0 (a read-only global's partial payload granule, the 0xf9 redzone granules after
   it), where DgnTransportBCg.v trans_sh_any_zshadow, which asks the whole hull inside one zero-shadow range, does
   not apply.
   - trans_sh_cell g v: the shadow byte of the granule at g reads v at every AR state (a constant cell of the record,
     trans_sh_cell_const, or a granule of a zero-shadow range, trans_sh_cell_zshadow);
   - trans_sh_cells cs: trans_sh_cell of every (granule, value) row of the list cs;
   - trans_cs_cover cs q n: a closed check that every granule of the 64-byte hull of [q, q + n) has a row in cs and
     every byte x of [q, q + n) is addressable by the row v of its granule (YG0v.v saddr_ok x v);
   - trans_sh_any_cells: from trans_sh_cells cs and trans_cs_cover cs q n = true, trans_sh_any of [q, q + n). *)
Section shc. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.

Definition trans_sh_cell (g v : Z) : Prop :=
  forall ly S (W : world segs) mem md, @AR rc segs B ly S W mem md ->
    aview segs (w_H W) mem (shadow_addr g) = Some v.

Lemma trans_sh_cell_const (g v : Z) :
  (forall ly, In (z1 (ANum (FCells.shadow_addr g)) v) (as_const B ly)) -> 0 <= v < 256 -> trans_sh_cell g v.
Proof.
  intros HC Hv ly S W mem md (M & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (HC ly)) as Hh.
  unfold cell_holds in Hh. cbn [z1 c1 c_at c_val c_w aeval] in Hh.
  specialize (Hh 0%nat ltac:(lia)).
  replace (FCells.shadow_addr g + Z.of_nat 0) with (shadow_addr g) in Hh
    by (unfold FCells.shadow_addr, FCells.ASAN_K, shadow_addr, SHADOW_OFF; lia).
  rewrite Hh. f_equal. unfold le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small v (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
  apply Z.mod_small. exact Hv.
Qed.

Lemma trans_sh_cell_zshadow (lo hi g : Z) :
  decode_zshadow_at B lo hi -> g mod 8 = 0 -> lo <= g -> g + 8 <= hi -> trans_sh_cell g 0.
Proof.
  intros HZ Hg H1 H2 ly S W mem md HAR.
  replace (shadow_addr g) with (FCells.shadow_addr g)
    by (unfold FCells.shadow_addr, FCells.ASAN_K, shadow_addr, SHADOW_OFF; lia).
  exact (decode_zshadow_rd B ly S W mem md lo hi g HAR Hg H1 H2 HZ).
Qed.

Definition trans_sh_cells (cs : list (Z * Z)) : Prop := forall c, In c cs -> trans_sh_cell (fst c) (snd c).

Lemma trans_sh_cells_nil : trans_sh_cells [].
Proof. intros c Hc. destruct Hc. Qed.

Lemma trans_sh_cells_cons (g v : Z) (cs : list (Z * Z)) :
  trans_sh_cell g v -> trans_sh_cells cs -> trans_sh_cells ((g, v) :: cs).
Proof. intros H1 H2 c [<-|Hc]; [exact H1 | exact (H2 c Hc)]. Qed.

Lemma trans_sh_cells_app (cs1 cs2 : list (Z * Z)) :
  trans_sh_cells cs1 -> trans_sh_cells cs2 -> trans_sh_cells (cs1 ++ cs2).
Proof. intros H1 H2 c Hc. apply in_app_or in Hc as [Hc|Hc]; [exact (H1 c Hc) | exact (H2 c Hc)]. Qed.

Lemma trans_sh_cells_const (L : list Z) (v : Z) :
  (forall ly a, In a L -> In (z1 (ANum (FCells.shadow_addr a)) v) (as_const B ly)) -> 0 <= v < 256 ->
  trans_sh_cells (map (fun a => (a, v)) L).
Proof.
  intros HC Hv c Hc. apply in_map_iff in Hc as (a & <- & Ha). cbn [fst snd].
  exact (trans_sh_cell_const a v (fun ly => HC ly a Ha) Hv).
Qed.

Definition trans_zgran (lo hi : Z) : list (Z * Z) :=
  map (fun i => (lo + 8 * Z.of_nat i, 0)) (seq 0 (Z.to_nat ((hi - lo) / 8))).

Lemma trans_sh_cells_zshadow (lo hi : Z) :
  decode_zshadow_at B lo hi -> lo mod 8 = 0 -> trans_sh_cells (trans_zgran lo hi).
Proof.
  intros HZ Hlo c Hc. unfold trans_zgran in Hc. apply in_map_iff in Hc as (i & <- & Hi).
  apply in_seq in Hi. cbn [fst snd].
  assert (Hd : Z.of_nat i < (hi - lo) / 8) by lia.
  pose proof (Z.mul_div_le (hi - lo) 8 ltac:(lia)) as Hm.
  apply (trans_sh_cell_zshadow lo hi); [exact HZ | | lia | lia].
  replace (lo + 8 * Z.of_nat i) with (lo + Z.of_nat i * 8) by ring. rewrite Z_mod_plus_full. exact Hlo.
Qed.

Definition trans_cs_find (cs : list (Z * Z)) (g : Z) : option Z :=
  match find (fun c => Z.eqb (fst c) g) cs with Some c => Some (snd c) | None => None end.
Definition trans_saddr_b (x v : Z) : bool := (v =? 0) || ((x mod 8 <? v) && (v <? 8)).
Definition trans_cs_cover (cs : list (Z * Z)) (q n : Z) : bool :=
  forallb (fun i => match trans_cs_find cs (q / 64 * 64 + 8 * Z.of_nat i) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) / 8))) &&
  forallb (fun i => match trans_cs_find cs ((q + Z.of_nat i) / 8 * 8) with
                    | Some v => trans_saddr_b (q + Z.of_nat i) v
                    | None => false
                    end)
    (seq 0 (Z.to_nat n)).

Lemma trans_cs_find_cell (cs : list (Z * Z)) (g v : Z) :
  trans_sh_cells cs -> trans_cs_find cs g = Some v -> trans_sh_cell g v.
Proof.
  intros HC Hf. unfold trans_cs_find in Hf.
  destruct (find (fun c => fst c =? g) cs) as [c|] eqn:E; [|discriminate Hf].
  injection Hf as <-. apply find_some in E as [Hin Heq]. cbv beta in Heq. apply Z.eqb_eq in Heq. rewrite <- Heq.
  exact (HC c Hin).
Qed.

Lemma trans_vrow_ra (rd : Z -> option Z) (lo hi q n : Z) :
  (forall T, T mod 8 = 0 -> lo <= T -> T + 8 <= hi -> rd (shadow_addr T) <> None) ->
  (forall x, q <= x < q + n -> exists s, rd (shadow_addr (x / 8 * 8)) = Some s /\ saddr_ok x s) ->
  lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi ->
  range_addressable rd SHADOW_OFF q n /\ shadow_hull_vis rd q n.
Proof.
  intros HV HA Hlo Hhi.
  pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)).
  split.
  - intros x Hx. destruct (HA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr (x / 8 * 8))
      by (unfold shadow_of_addr, shadow_addr; rewrite Z.div_mul by lia; reflexivity).
    exact Hs.
  - intros s Hs.
    assert (ES : shadow_addr ((s - SHADOW_OFF) * 8) = s) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
    rewrite <- ES. apply HV; [apply Z_mod_mult | |].
    all: unfold shadow_addr, SHADOW_OFF in Hs |- *.
    all: pose proof (Z.div_mod q 8 ltac:(lia)); pose proof (Z.mod_pos_bound q 8 ltac:(lia));
      pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia));
      pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia));
      pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)); lia.
Qed.

Lemma trans_sh_any_cells (cs : list (Z * Z)) (q n : Z) :
  trans_sh_cells cs -> trans_cs_cover cs q n = true -> trans_sh_any B q n.
Proof.
  intros HC Hcov ly S W mem md HAR.
  unfold trans_cs_cover in Hcov. apply andb_true_iff in Hcov as [HG HX].
  rewrite forallb_forall in HG, HX. cbv beta in HG, HX.
  pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)).
  apply (trans_vrow_ra _ (q / 64 * 64) ((q + n - 1) / 64 * 64 + 64) q n); [| | lia | lia].
  - intros T HT HT1 HT2.
    pose proof (Z.div_mod T 8 ltac:(lia)).
    pose proof (Z.div_mod (T - q / 64 * 64) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (T - q / 64 * 64) 8 ltac:(lia)).
    pose proof (Z.div_mod ((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound ((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) 8 ltac:(lia)).
    assert (Hd : 0 <= (T - q / 64 * 64) / 8 < ((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) / 8) by lia.
    assert (ET : q / 64 * 64 + 8 * Z.of_nat (Z.to_nat ((T - q / 64 * 64) / 8)) = T)
      by (rewrite Z2Nat.id by lia; lia).
    pose proof (HG (Z.to_nat ((T - q / 64 * 64) / 8)) ltac:(apply in_seq; lia)) as HGi.
    rewrite ET in HGi.
    revert HGi. destruct (trans_cs_find cs T) as [v|] eqn:Ef; intro HGi; [|discriminate HGi].
    rewrite (trans_cs_find_cell cs T v HC Ef ly S W mem md HAR). discriminate.
  - intros x Hx.
    pose proof (HX (Z.to_nat (x - q)) ltac:(apply in_seq; lia)) as HXi.
    rewrite Z2Nat.id in HXi by lia. replace (q + (x - q)) with x in HXi by lia.
    revert HXi. destruct (trans_cs_find cs (x / 8 * 8)) as [v|] eqn:Ef; intro HXi; [|discriminate HXi].
    exists v. split; [exact (trans_cs_find_cell cs (x / 8 * 8) v HC Ef ly S W mem md HAR)|].
    unfold trans_saddr_b in HXi. unfold saddr_ok.
    apply orb_true_iff in HXi as [Hb|Hb]; [left; apply Z.eqb_eq in Hb; exact Hb | right].
    apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. lia.
Qed.
End shc.

(* 2b. The cover list of this function: the payload rows of transport_cells (whole and partial granules), the 0xf9
   guard granules of trans_llvmf_cells (TRANS_LLVMF_F9) and the zero-shadow ranges of transport_cells, as granules. *)
Definition lc_cs : list (Z * Z) :=
  [(TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_SPEC_OUI, 3); (TRANS_STR_C24 + 8, 1);
   (TRANS_STR_PC + 8, 1); (TRANS_CMD, 7); (TRANS_DESK2, 6); (TRANS_NOTDD, 6); (TRANS_OTHER, 6); (TRANS_STR4, 6)] ++
  map (fun a => (a, 0xf9)) TRANS_LLVMF_F9 ++
  trans_zgran TRANS_STR_C24 (TRANS_STR_C24 + 8) ++ trans_zgran TRANS_STR_PC (TRANS_STR_PC + 8) ++
  trans_zgran TRANS_IO (TRANS_IO + 32).

(* build_and_receive's dst / src (HOST, DESK, SPEC_BCAST, OTHER, DESK2, NOTDD), strlen's [x, x + k] and
   [x, x + k + 1) for the three names, io. *)
Definition lc_ro_ranges : list (Z * Z) :=
  [(TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_OTHER, 6); (TRANS_DESK2, 6); (TRANS_NOTDD, 6);
   (TRANS_STR_C24, 8); (TRANS_STR_C24, 9); (TRANS_STR_PC, 8); (TRANS_STR_PC, 9); (TRANS_STR4, 5); (TRANS_STR4, 6);
   (TRANS_IO, 32)].

Lemma lc_cover : forallb (fun r => trans_cs_cover lc_cs (fst r) (snd r)) lc_ro_ranges = true.
Proof. vm_compute. reflexivity. Qed.
(* Not vacuous: HOST's seventh byte is a redzone byte of its partial granule. *)
Lemma lc_cover_neg : trans_cs_cover lc_cs TRANS_HOST 7 = false.
Proof. vm_compute. reflexivity. Qed.

Section sh. Context {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma lc_sh_cells (ly0 : alayout) : transport_cells B -> trans_llvmf_cells B -> trans_sh_cells B lc_cs.
Proof.
  intros HC (_ & HL).
  destruct (HC ly0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HZc & _ & HZp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HZio & _).
  unfold lc_cs. apply trans_sh_cells_app.
  { repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
    all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
  apply trans_sh_cells_app.
  { apply trans_sh_cells_const; [intros ly a Ha; exact (proj2 (HL ly) a Ha) | lia]. }
  apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZc | reflexivity]|].
  apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZp | reflexivity]|].
  apply trans_sh_cells_zshadow; [exact HZio | reflexivity].
Qed.

Lemma lc_sh_any (ly0 : alayout) : transport_cells B -> trans_llvmf_cells B ->
  forall r, In r lc_ro_ranges -> trans_sh_any B (fst r) (snd r).
Proof.
  intros HC HL r Hr. apply (trans_sh_any_cells B lc_cs); [exact (lc_sh_cells ly0 HC HL)|].
  pose proof lc_cover as K. rewrite forallb_forall in K. exact (K r Hr).
Qed.
End sh.

(* The read-only bytes the walk reads, copies or hands a callee, as the image holds them (decided over the loaded
   segments): the six MACs, io's 32 bytes (the four words of __const.LLVMFuzzerTestOneInput.io), op_frame.CMD,
   SCALE, the divisor constants of `name mod 3` (TRANS_K_LLVMF, +0xd5c) and `len mod 22` (TRANS_K_LLVMF2, +0x100c),
   the pointer tables op_frame.DST / SRC and op_announce.NAME, the three name strings with their NUL, and the
   op switch's table (8 entries, ops 0 .. 7: op 8 leaves at `bltu a1, a0`; each the target's distance from the
   table, `add a0, a0, a1` at +0x5ec). *)
Definition lc_rom_tab : list (Z * list byte) :=
  [(TRANS_HOST, TC.HOST); (TRANS_DESK, TC.DESK); (TRANS_SPEC_BCAST, TC.SPEC_BCAST); (TRANS_OTHER, TC.OTHER);
   (TRANS_DESK2, TC.DESK2); (TRANS_NOTDD, TC.NOTDD);
   (TRANS_IO, sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B) (TI.ti_io_now timg_B));
   (TRANS_CMD, map DSpec.b8 TOP.op_frame_CMD);
   (TRANS_SCALE, flat_map (TW.put 8) TOP.LLVMFuzzerTestOneInput_SCALE);
   (TRANS_K_LLVMF, TW.put 8 0x5555555555555556); (TRANS_K_LLVMF2, TW.put 8 0x0ba2e8ba2e8ba2e9);
   (TRANS_DST, flat_map (TW.put 8) [TRANS_HOST; TRANS_SPEC_BCAST; TRANS_OTHER; TRANS_HOST]);
   (TRANS_SRC, flat_map (TW.put 8) [TRANS_DESK; TRANS_DESK2; TRANS_HOST; TRANS_NOTDD]);
   (TRANS_NAME, flat_map (TW.put 8) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4]);
   (TRANS_STR_C24, nth 0 TOP.op_announce_NAME [] ++ [DSpec.b8 0]);
   (TRANS_STR_PC, nth 1 TOP.op_announce_NAME [] ++ [DSpec.b8 0]);
   (TRANS_STR4, nth 2 TOP.op_announce_NAME [] ++ [DSpec.b8 0]);
   (TRANS_JT_LLVMF, flat_map (fun t => TW.put 4 (t - TRANS_JT_LLVMF))
      (map (fun o => transportb_text + o) (firstn 8 LO_ARMS)))].
Definition lc_rom_ok_b : bool :=
  forallb (fun e => forallb (fun i =>
    match YK11.seg_rom tfibsegs (Z_to_bv 64 (fst e + Z.of_nat i)) with
    | Some b => bv_unsigned b =? bv_unsigned (nth i (snd e) (Z_to_bv 8 0))
    | None => false
    end) (seq 0 (length (snd e)))) lc_rom_tab.
Lemma lc_rom_ok : lc_rom_ok_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lc_rom_bytes : forall q l, In (q, l) lc_rom_tab -> forall i, (i < length l)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (q + Z.of_nat i))) =
  Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
intros q l Hin i Hi. pose proof lc_rom_ok as K. unfold lc_rom_ok_b in K. rewrite forallb_forall in K.
specialize (K (q, l) Hin). rewrite forallb_forall in K. specialize (K i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))).
cbn [fst snd] in K. destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 (q + Z.of_nat i))) as [b|]; [|discriminate K].
apply Z.eqb_eq in K. cbn [option_map]. rewrite K. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The model bridges                                                 *)
(* ------------------------------------------------------------------ *)

(* The prologue: below the size bound, LLVMFuzzerTestOneInput_m is lc_pro_m, the abort test and the loop from
   InitOk.prologue_cursor. *)
Lemma lc_pro_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte),
  Z.of_nat (length D) < TOP.FUZZ_INPUT_MAX ->
  TOP.LLVMFuzzerTestOneInput_m I B A D =
  match lc_pro_m I B D with
  | None => None
  | Some (B25, r) =>
      if negb (r =? DSpec.SPEC_OK) then None
      else match TOP.LLVMFuzzerTestOneInput_loop_m (Z.to_nat TC.OPS_MAX) I B25 A D (IOK.prologue_cursor D) O with
           | Some (B26, _) => Some (B26, 0)
           | None => None
           end
  end.
Proof.
intros I B A D HD.
unfold TOP.LLVMFuzzerTestOneInput_m, lc_pro_m, lc_pro_scal, IOK.prologue_cursor. cbv zeta.
rewrite (proj2 (Z.leb_gt TOP.FUZZ_INPUT_MAX (Z.of_nat (length D))) HD).
destruct (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))) as [c1 flags].
destruct (TS0.diginet_session_config_default_m B) as [[B1 []]|]; [|reflexivity].
destruct (TOP.fuzz_u8_m D c1) as [c2 v1].
destruct (TOP.fuzz_u8_m D c2) as [c3 v2].
destruct (TOP.fuzz_u16_m D c3) as [c4 v3].
destruct (TOP.fuzz_u8_m D c4) as [c5 v4].
destruct (TOP.fuzz_u16_m D c5) as [c6 v5].
destruct (TOP.fuzz_u16_m D c6) as [c7 v6].
destruct (TOP.fuzz_u16_m D c7) as [c8 v7].
destruct (TOP.fuzz_u8_m D c8) as [c9 v8].
destruct (TOP.fuzz_u16_m D c9) as [c10 v9].
unfold lc_pro_minit. cbv zeta.
reflexivity.
Qed.

(* The op code's arm: the op byte read and the comparisons of TOps.v :290-328 at the code. *)
Local Ltac opc_arm D c Ho :=
  unfold lc_opc, lc_oc in *; unfold TOP.LLVMFuzzerTestOneInput_op_m;
  destruct (TOP.fuzz_u8_m D c) as [c1 opb]; cbn [fst snd] in *; cbv zeta; rewrite Ho;
  repeat match goal with |- context [?x =? ?y] =>
    let v := eval vm_compute in (x =? y) in
    lazymatch v with true => change (x =? y) with true | false => change (x =? y) with false end end;
  cbv beta iota.

(* Ops 0 and 8: one call of receive, of the record lc_recv_vals names. *)
Lemma lc_recv_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 0 \/ lc_opc D c = 8 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  match TOP.receive_m I B (A k) (TW.sub D (rv_off (lc_recv_vals D c)) (Z.to_nat (rv_n (lc_recv_vals D c))))
          (rv_bp (lc_recv_vals D c)) (rv_pf (lc_recv_vals D c)) with
  | Some (B1, _) => Some (B1, (rv_c (lc_recv_vals D c), S k))
  | None => None
  end.
Proof.
intros I B A D c k [Ho | Ho].
- unfold lc_recv_vals. opc_arm D c Ho.
  destruct (TOP.fuzz_record_m D c1) as [[c2 off] n]. cbn [rv_off rv_n rv_bp rv_pf rv_c].
  destruct (TOP.receive_m I B (A k) (TW.sub D off (Z.to_nat n)) 0 0) as [[B1 []]|]; reflexivity.
- unfold lc_recv_vals. opc_arm D c Ho.
  destruct (TOP.fuzz_u8_m D c1) as [c2 pf]. cbv zeta.
  destruct (TOP.fuzz_record_m D c2) as [[c3 off] n]. cbn [rv_off rv_n rv_bp rv_pf rv_c].
  destruct (TOP.receive_m I B (A k) (TW.sub D off (Z.to_nat n)) 1 pf) as [[B1 []]|]; reflexivity.
Qed.

(* Op 1: one call of build_and_receive, of the values lc_frame_vals names. *)
Lemma lc_frame_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 1 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  let fv := lc_frame_vals D B (lc_oc D c) in
  match TOP.build_and_receive_m I B (A k) (lc_fdst (fv_sel fv)) (lc_fsrc (fv_sel fv)) (fv_send fv) (fv_ack fv)
          (fv_retry fv) (lc_fcmd (fv_sel fv)) (TW.sub D (fv_off fv) (Z.to_nat (fv_len fv))) with
  | Some (B1, _) => Some (B1, (fv_c fv, S k))
  | None => None
  end.
Proof.
intros I B A D c k Ho. unfold lc_frame_vals, lc_fdst, lc_fsrc, lc_fcmd. opc_arm D c Ho.
unfold TOP.op_frame_m.
destruct (TOP.fuzz_u8_m D c1) as [c1' sel].
destruct (TOP.fuzz_u16_m D c1') as [c2 send].
destruct (TOP.fuzz_u16_m D c2) as [c3 ack0].
destruct (TOP.fuzz_u8_m D c3) as [c4 r].
destruct (TOP.fuzz_u16_m D c4) as [c5 w].
cbv zeta.
destruct (TOP.fuzz_take_m c5 (w mod (TC.SPEC_MAX_BODY + 1))) as [[c6 off] len].
cbn [fv_sel fv_send fv_ack fv_retry fv_off fv_len fv_c].
match goal with |- context [TOP.build_and_receive_m ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10] =>
  destruct (TOP.build_and_receive_m a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) as [[B1 []]|] end; reflexivity.
Qed.

(* Op 2: one call of build_and_receive with the body lc_ann_vals names. *)
Lemma lc_ann_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 2 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  let av := lc_ann_vals D (lc_oc D c) in
  match TOP.build_and_receive_m I B (A k) TC.SPEC_BCAST TC.DESK 0 0 0 (lc_acmd (av_sel av)) (av_body3 av) with
  | Some (B1, _) => Some (B1, (av_c av, S k))
  | None => None
  end.
Proof.
intros I B A D c k Ho. unfold lc_ann_vals, lc_acmd. opc_arm D c Ho.
unfold TOP.op_announce_m.
destruct (TOP.fuzz_u8_m D c1) as [c1' sel].
destruct (TOP.fuzz_u8_m D c1') as [c2 m].
destruct (TOP.fuzz_u8_m D c2) as [c3 nm].
cbv zeta. cbn [av_sel av_body3 av_c].
match goal with |- context [TOP.build_and_receive_m ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10] =>
  destruct (TOP.build_and_receive_m a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) as [[B1 []]|] end; reflexivity.
Qed.

(* Op 3: op_begin, the g_now store (lc_tick_w), m_tick, diginet_session_tick, settle 1. *)
Lemma lc_tick_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 3 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  match TC.op_begin_m B with
  | Some (B1, _) =>
      match TC.m_tick_m (lc_tick_w D (lc_oc D c) B1) with
      | Some (B3, _) =>
          match TSS.diginet_session_tick_m I None B3 (TW.g_now B3) with
          | Some (B4, _) =>
              match TC.settle_m B4 1 with
              | Some (B5, _) => Some (B5, (lc_tick_c D (lc_oc D c), k))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.
Proof.
intros I B A D c k Ho. unfold lc_tick_w, lc_tick_c. opc_arm D c Ho.
destruct (TOP.fuzz_u8_m D c1) as [c2 sb]. cbv zeta.
destruct (TC.op_begin_m B) as [[B1 []]|]; [|reflexivity].
destruct (TOP.fuzz_u16_m D c2) as [c3 t]. cbv zeta. cbn [fst].
reflexivity.
Qed.

(* Op 4: op_submit. *)
Lemma lc_op4_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 4 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  match TOP.op_submit_m B D (lc_oc D c) with
  | Some (B1, c2) => Some (B1, (c2, k))
  | None => None
  end.
Proof. intros I B A D c k Ho. opc_arm D c Ho. reflexivity. Qed.

(* op_submit, raw mode: the struct lc_raw_cs, diginet_session_submit, check_refusal_submit, settle 0. *)
Lemma lc_submit_raw_eq : forall (B B1 D : list byte) (c1 : TOP.fuzz_in),
  TC.op_begin_m B = Some (B1, tt) -> TW.g_raw B1 <> 0 ->
  TOP.op_submit_m B D c1 =
  let kd := lc_sub_kd D c1 in
  let rv := lc_raw_vals D (sv_c kd) in
  let cs := lc_raw_cs D rv (sv_display kd) (sv_key kd) in
  match TS0.diginet_session_submit_m B1 cs with
  | Some (B2, rc) =>
      match TC.check_refusal_submit_m B2 cs rc (TW.S_queued B) with
      | Some (B3, _) =>
          match TC.settle_m B3 0 with
          | Some (B4, _) => Some (B4, rw_c rv)
          | None => None
          end
      | None => None
      end
  | None => None
  end.
Proof.
intros B B1 D c1 HOB HR. unfold TOP.op_submit_m, lc_sub_kd, lc_raw_vals, lc_raw_cs. cbv zeta.
rewrite HOB. cbv beta iota.
destruct (TOP.fuzz_u8_m D c1) as [c1' kb].
destruct (TOP.fuzz_u8_m D c1') as [c2 ab].
destruct (TOP.fuzz_u8_m D c2) as [c3 db].
cbv zeta. cbn [sv_key sv_display sv_c].
rewrite (proj2 (Z.eqb_neq (TW.g_raw B1) 0) HR). cbv beta iota delta [negb].
destruct (TOP.fuzz_u16_m D c3) as [c4 w].
destruct (TOP.fuzz_take_m c4 (w mod (DSpec.SPEC_CMD_MAX + 1))) as [[c5 off] t].
cbn [rw_len rw_off rw_t rw_c]. cbv zeta.
reflexivity.
Qed.

(* The raw mode's take from the length word the code holds in a1 at SUBR (lc_raw_w) and the cursor after it
   (lc_raw_c4). *)
Lemma lc_raw_vals_eq : forall (D : list byte) (c3 : TOP.fuzz_in),
  lc_raw_vals D c3 =
  let '(c5, off, t) := TOP.fuzz_take_m (lc_raw_c4 D c3) (lc_raw_w D c3 mod (DSpec.SPEC_CMD_MAX + 1)) in
  mkLrw (t mod 2^8) off t c5.
Proof.
intros D c3. unfold lc_raw_vals, lc_raw_c4, lc_raw_w.
destruct (TOP.fuzz_u16_m D c3) as [c4 w]. reflexivity.
Qed.

(* op_submit, tagged mode: lc_tag_vals, sys / at / want (lc_sys, lc_at, lc_want), diginet_session_submit,
   check_refusal_submit, check_latest_submit unless sys, the stores of g_cmd[serial] and the queue when want =
   SPEC_OK (TOps.v :258-272), g_ncmd + 1 and settle 0. *)
Lemma lc_submit_tag_eq : forall (B B1 D : list byte) (c1 : TOP.fuzz_in),
  TC.op_begin_m B = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  TOP.op_submit_m B D c1 =
  let kd := lc_sub_kd D c1 in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  let serial := tg_serial tv in
  let len := tg_len tv in
  let cbytes := tg_cbytes tv in
  let key := sv_key kd in
  let display := sv_display kd in
  if TC.CMDS_MAX <=? serial then None
  else
    match lc_at tv key with
    | None => None
    | Some at_ =>
        let want := lc_want tv at_ in
        let cs := TOP.cmd_struct cbytes len display key in
        match TS0.diginet_session_submit_m (tg_B2 tv) cs with
        | None => None
        | Some (B3, rc) =>
            match TC.check_refusal_submit_m B3 cs rc (TW.S_queued B) with
            | None => None
            | Some (B4, _) =>
                match (if lc_sys tv then Some (B4, tt) else TC.check_latest_submit_m B4 rc want) with
                | None => None
                | Some (B5, _) =>
                    match (if want =? DSpec.SPEC_OK then
                             let Bw := TW.set_Cmd_bytes
                                         (TW.set_Cmd_len (TW.set_Cmd_display (TW.set_Cmd_key
                                            (TW.set_Cmd_st B5 serial TC.PENDING) serial key) serial display)
                                            serial len)
                                         serial (firstn (Z.to_nat len) cbytes) in
                             if 0 <=? at_ then
                               let q := TW.Q_at Bw at_ in
                               if TC.CMDS_MAX <=? q then None
                               else Some (TW.set_Q_at (TW.set_Cmd_st Bw q TC.REPLACED) at_ serial)
                             else
                               let nq := TW.g_nq Bw in
                               if TC.CMDS_MAX <=? nq then None
                               else Some (TW.set_g_nq (TW.set_Q_at Bw nq serial) ((nq + 1) mod 2^32))
                           else Some B5) with
                    | None => None
                    | Some B6 =>
                        let B7 := TW.set_g_ncmd B6 ((TW.g_ncmd B6 + 1) mod 2^32) in
                        match TC.settle_m B7 0 with
                        | None => None
                        | Some (B8, _) => Some (B8, tg_c tv)
                        end
                    end
                end
            end
        end
    end.
Proof.
intros B B1 D c1 HOB HR. unfold TOP.op_submit_m, lc_sub_kd, lc_tag_vals, lc_at, lc_want, lc_sys. cbv zeta.
rewrite HOB. cbv beta iota.
destruct (TOP.fuzz_u8_m D c1) as [c1' kb].
destruct (TOP.fuzz_u8_m D c1') as [c2 ab].
destruct (TOP.fuzz_u8_m D c2) as [c3 db].
cbv zeta. cbn [sv_key sv_display sv_c].
rewrite HR. change (negb (0 =? 0)) with false. cbv beta iota.
destruct (TOP.fuzz_u8_m D c3) as [c4 lb]. cbv zeta.
destruct (TOP.fuzz_take_m c4 (lb mod 22 + 3 - 3)) as [[c5 off] n].
cbn [tg_serial tg_B2 tg_len tg_off tg_n tg_cbytes tg_c tg_c4]. cbv zeta.
reflexivity.
Qed.

(* Op 5: op_begin, m_wake, diginet_session_wake, check_state_wake_code, settle 0. *)
Lemma lc_op5_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 5 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  match TC.op_begin_m B with
  | Some (B1, _) =>
      match TC.m_wake_m B1 with
      | Some (B2, want) =>
          match TSS.diginet_session_wake_m I None B2 (TW.g_now B2) with
          | Some (B3, rc) =>
              match TC.check_state_wake_code_m B3 rc want with
              | Some (B4, _) =>
                  match TC.settle_m B4 0 with
                  | Some (B5, _) => Some (B5, (lc_oc D c, k))
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.
Proof. intros I B A D c k Ho. opc_arm D c Ho. reflexivity. Qed.

(* Op 6: op_begin, m_close, diginet_session_close, settle 0. *)
Lemma lc_op6_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 6 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k =
  match TC.op_begin_m B with
  | Some (B1, _) =>
      match TC.m_close_m B1 with
      | Some (B2, _) =>
          match TSS.diginet_session_close_m I None B2 (TW.g_now B2) with
          | Some (B3, _) =>
              match TC.settle_m B3 0 with
              | Some (B4, _) => Some (B4, (lc_oc D c, k))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.
Proof. intros I B A D c k Ho. opc_arm D c Ho. reflexivity. Qed.

(* m_close is lc_close_w, then the call of m_set at (S_CLOSED, R_CLOSED) (TCb.v :378-386; image B calls m_set at
   +0x8e8). *)
Lemma lc_close_eq : forall (B : list byte),
  TC.m_close_m B =
  match lc_close_w B with
  | Some B2 => TC.m_set_m B2 TC.S_CLOSED TC.R_CLOSED
  | None => None
  end.
Proof.
intros B. unfold TC.m_close_m, lc_close_w.
destruct (TC.truth (TW.M_desk_known B) && negb (TC.truth (TW.M_foreign B)) && negb (TW.M_state B =? TC.S_CLOSED));
  [|reflexivity].
destruct (TC.int_inc (TW.OW_e3 B)); reflexivity.
Qed.

(* Op 7: g_fail_next = 1. *)
Lemma lc_op7_eq : forall (I : TI.timg) (B : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat),
  lc_opc D c = 7 ->
  TOP.LLVMFuzzerTestOneInput_op_m I B A D c k = Some (TW.set_g_fail_next B 1, (lc_oc D c, k)).
Proof. intros I B A D c k Ho. opc_arm D c Ho. reflexivity. Qed.

(* settle keeps the world it is given: each of its checks answers Some (B, tt) or None (TCb.v settle_m :659-667). *)
Local Ltac lc_keep H B :=
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x; cbv beta iota zeta in H
  end;
  try discriminate H;
  exact (eq_sym (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H)).
Lemma lc_cas_keep : forall B B1 u, TC.check_ack_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_ack_settle_m in H. lc_keep H B. Qed.
Lemma lc_css_keep : forall B B1 u, TC.check_state_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_state_settle_m in H. lc_keep H B. Qed.
Lemma lc_cis_keep : forall B B1 u, TC.check_inflight_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_inflight_settle_m in H. lc_keep H B. Qed.
Lemma lc_cks_keep : forall B B1 u, TC.check_keepalive_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_keepalive_settle_m in H. lc_keep H B. Qed.
Lemma lc_clq_keep : forall B B1 u, TC.check_latest_queue_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_latest_queue_m in H. lc_keep H B. Qed.
Lemma lc_cld_keep : forall B B1 u, TC.check_latest_drain_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_latest_drain_m in H. lc_keep H B. Qed.
Lemma lc_settle_world : forall (B B' : list byte) (t : Z) (u : unit), TC.settle_m B t = Some (B', u) -> B' = B.
Proof.
intros B B' t u H. unfold TC.settle_m in H.
destruct (TC.check_ack_settle_m B) as [[B1 u1]|] eqn:E1; [|discriminate H].
rewrite (lc_cas_keep B B1 u1 E1) in H.
destruct (TC.check_state_settle_m B) as [[B2 u2]|] eqn:E2; [|discriminate H].
rewrite (lc_css_keep B B2 u2 E2) in H.
destruct (TC.check_inflight_settle_m B) as [[B3 u3]|] eqn:E3; [|discriminate H].
rewrite (lc_cis_keep B B3 u3 E3) in H.
destruct (TC.check_keepalive_settle_m B) as [[B4 u4]|] eqn:E4; [|discriminate H].
rewrite (lc_cks_keep B B4 u4 E4) in H.
destruct (negb (TC.truth (TW.g_raw B))).
- destruct (TC.check_latest_queue_m B) as [[B5 u5]|] eqn:E5; [|discriminate H].
  rewrite (lc_clq_keep B B5 u5 E5) in H.
  destruct (TC.truth t).
  + exact (lc_cld_keep B B' u H).
  + exact (eq_sym (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H)).
- exact (eq_sym (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H)).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The simulation step at the loop tail                              *)
(* ------------------------------------------------------------------ *)

(* Two Some answers of one option are equal, read component by component (no inversion of the world). *)
Lemma lc_some3 : forall {T U V : Type} (o : option (T * (U * V))) (x x' : T) (y y' : U) (z z' : V),
  o = Some (x, (y, z)) -> o = Some (x', (y', z')) -> x = x' /\ y = y' /\ z = z'.
Proof.
intros T U V o x x' y y' z z' E1 E2. rewrite E1 in E2.
split; [exact (f_equal (fun o => match o with Some (a, _) => a | None => x end) E2)|].
split; [exact (f_equal (fun o => match o with Some (_, (b, _)) => b | None => y end) E2)|].
exact (f_equal (fun o => match o with Some (_, (_, c)) => c | None => z end) E2).
Qed.

(* The operation's equation at the stream fun _ => a, recv_addr_ok a, from a head where the simulation invariant
   holds: agree timg_B (ops + 1) at its world, the cursor in range, and at most ops + 1 receptions. *)
Lemma lc_tail_agree : forall (D : list byte) (ops : Z) (B0 : list byte) (c0 : TOP.fuzz_in) (k0 : nat)
    (a : Z) (Bw : list byte) (cn : TOP.fuzz_in) (k' : nat),
  AG.agree timg_B ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  Z.of_nat k0 <= ops -> recv_addr_ok a ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 (fun _ => a) D c0 k0 = Some (Bw, (cn, k')) ->
  AG.agree timg_B (ops + 1) Bw /\ QF.fuzz_in_ok D cn /\ Z.of_nat k' <= ops + 1.
Proof.
intros D ops B0 c0 k0 a Bw cn k' HA Hops Hc Hn Hk (Ha1 & Ha2) E.
destruct (LOK.op_ok LP.links_holds timg_B ops B0 (fun _ => a) D c0 k0 HA Hops Hc Hn Ha1 Ha2)
  as (B' & c' & k'' & E' & HA' & Hc').
destruct (lc_some3 _ Bw B' cn c' k' k'' E E') as (EB & EC & EK).
subst B' c' k''.
pose proof (LOK.op_k_of timg_B B0 (fun _ => a) D c0 k0 Bw cn k' E) as Hk'.
split; [exact HA'|]. split; [exact Hc'|]. destruct Hk' as [-> | ->]; lia.
Qed.

(* The tail's cut gives the next head's simulation facts: lc_opok at operation ops + 1 when bytes are left. *)
Lemma lc_tail_opok : forall (D : list byte) (ops : Z) (B0 : list byte) (c0 : TOP.fuzz_in) (k0 : nat)
    (a : Z) (Bw : list byte) (cn : TOP.fuzz_in) (k' : nat),
  AG.agree timg_B ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  Z.of_nat k0 <= ops -> recv_addr_ok a ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 (fun _ => a) D c0 k0 = Some (Bw, (cn, k')) ->
  ops + 1 < TC.OPS_MAX -> TOP.fi_n cn <> 0 ->
  AG.agree timg_B (ops + 1) Bw /\ 0 <= ops + 1 < TC.OPS_MAX /\ QF.fuzz_in_ok D cn /\ TOP.fi_n cn <> 0 /\
  Z.of_nat k' <= ops + 1.
Proof.
intros D ops B0 c0 k0 a Bw cn k' HA Hops Hc Hn Hk Ha E Hlt Hn'.
destruct (lc_tail_agree D ops B0 c0 k0 a Bw cn k' HA Hops Hc Hn Hk Ha E) as (HA' & Hc' & Hk').
split; [exact HA'|]. split; [lia|]. split; [exact Hc'|]. split; [exact Hn'|]. exact Hk'.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The error exits and the segments that rule them out               *)
(* ------------------------------------------------------------------ *)

(* The 59 __asan_report_* calls and the abort pair of the listing, by the segment whose path reaches each (the
   control-flow regions between the cuts of LLVMFuzzerTestOneInput_segs.v; every report call is a no-return exit of
   its segment, refuted there from the shadow of the access it guards; the addresses are the calls'):
     HDR          0x82e04 load1   the flags byte at p (+0x26c: n > 0, so p .. p + n - 1 is a block's payload; ENTRY
                                  reaches it only on the real-stack path, which the flag word rules out)
     CFG          0x82e18 0x82e24 0x82e34 0x82e44 0x82e54 0x82e64 0x82e74 0x82e84 0x82e94 0x82ea4 0x82eb4 0x82ed8
                  0x82fe8 0x82ff8 load1   the 14 config bytes at the cursor (each read only while bytes are left)
     PRE          0x82de8 / 0x82dec   __asan_handle_no_return and abort after diginet_session_init (rc = SPEC_OK by
                                  the model: lc_pro_agree_stmt)
     HEAD         0x82f04 load1   the op byte at the cursor (n <> 0)
     OP0          0x82f2c 0x82f68 load1   the record length's two bytes
     OP8          0x82f3c 0x82f74 0x82fa4 load1   the poll flags byte and the record length's two bytes
     OP1          0x82b04 0x82f0c 0x82f34 0x82f58 0x82f6c 0x82f98 0x82f9c 0x82fc0 0x82fc8 load1, 0x82ec0 0x82ec8 load8
                  sel, send, ack, retry, w at the cursor; op_frame.CMD[(sel & 7) mod 7] (its shadow row 7);
                  op_frame.DST / SRC + 8 i, i < 4 (zero-shadow rows)
     OP2A         0x82f14 0x82f54 0x82f90 load1   sel, mac, name at the cursor
     OP2B         0x82ebc load8   op_announce.NAME + 8 (name mod 3)
     OP3A         0x82f24 0x82f4c 0x82f78 load1, 0x82eb8 load8   the scale byte and the u16; SCALE + 8 (byte & 3)
     OP4A         0x82f1c 0x82f44 0x82f60 0x82f80 0x82fbc load1   the key, address and display bytes and the raw
                                  length word's two bytes
     OP4T         0x82f88 load1   the len byte
     OP4SYS       0x82ee0 0x82ee8 0x82eec load1   c[i], c[i + 1], c[i + 3], i + 3 < len <= 24 (inside c, shadow 4 .. 7
                                  = 0 since +0x630)
     OP4FIND      0x82ef0 0x82ef8 load4   g_q + 4 i (i < g_nq <= QUEUE_MAX) and g_cmd + 40 g_q[i] + 4 (g_q[i] <
                                  CMDS_MAX: Agree.v agree_q d1_entry at lc_opok's world, or LoopOk.op_ok's Some
                                  through lc_submit_tag_eq), zero-shadow payloads (trans_settle_cells)
     OP4ST        0x82fac 0x82fb0 0x82fb4 0x82efc 0x82fd4 0x82fd8 store4, 0x82fb8 store1, 0x82fcc load4
                  g_cmd[serial]'s st / key / display / len, g_q[at], g_cmd[g_q[at]].st, g_q[old g_nq] (serial <
                  CMDS_MAX, at < g_nq, old g_nq < QUEUE_MAX by the want test)
   The other segments (MINIT, RECV, BAR1, BAR2, OP3B, OP4R, OP4COAL, OP4SUB, OP4S, OP5, OP6A, OP6M, OP6B, SET56, OP7,
   TAIL, EXIT) reach no report call. The checks of __asan_memcpy and __asan_memset are their contract's pre
   (aintrin_realizes).

   The 74 branches to the UBSan trap word 0x82de4 (+0x1b44; `jal` / `b*` whose target is the trap, at the pc of the
   branch), by the segment that runs each and the fact that refutes it (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v's
   seven groups):
     HDR     1   0x814f4 (cursor p + 1, the flags byte; ENTRY's region reaches it only after `beqz a2` at +0x068 is
                 taken, refuted there: the flag word is 1)
     CFG    14   0x81650 0x82b0c 0x82b48 0x82b78 0x82bb8 0x82bec 0x82c1c 0x82c58 0x82c84 0x82cc0 0x82cec 0x82d28
                 0x82d70 0x82dc0 (cursor p + 1, the config bytes)
     HEAD    1   0x81834 (cursor p + 1, the op byte)
     OP0     3   0x818a0 0x81e54 (cursor p + 1); 0x81e88 (fuzz_take p + n)
     OP8     4   0x81bb8 0x81f28 0x821f0 (cursor p + 1); 0x81ce8 (fuzz_take p + n)
     OP1    12   0x81a60 0x81eac 0x81ef8 0x82168 0x82198 0x821c4 0x825ec 0x82930 (cursor p + 1); 0x82654 (fuzz_take
                 p + n); 0x82674 0x826a4 0x826c8 (table index DST + 8 i, SRC + 8 i, CMD + i)
     OP2A    7   0x81994 0x819c4 0x81fe0 (cursor p + 1); 0x82054 0x8213c 0x82148 0x82150 (frame address body + mac,
                 body + mac - 10 null and wrap)
     OP2B    3   0x82070 0x82098 (frame address body + 15, body + 24); 0x820ac (table index NAME + 8 name)
     OP3A    4   0x81a04 0x81c6c 0x81f58 (cursor p + 1); 0x81a34 (table index SCALE + 8 (byte & 3))
     OP4A    5   0x81954 0x81d58 0x81db0 0x81df4 0x82534 (cursor p + 1)
     OP4R    1   0x825a0 (fuzz_take p + n)
     OP4T    5   0x8228c (cursor p + 1); 0x8232c 0x82330 (fuzz_take p + n, wrap and null); 0x82254 (index g_ncmd <=
                 1024); 0x82270 (g_cmd + 40 serial)
     OP4SYS  3   0x82354 0x82384 0x823ac (frame address c + i null, c + i + 1, c + i + 3)
     OP4FIND 3   0x8248c (index i <> 1024); 0x824a8 (index g_q[i] <= 1023); 0x824b8 (array g_cmd + 40 g_q[i])
     OP4ST   7   0x8277c (index serial <> 1024); 0x82780 (the g_cmd[serial] pointer <> 0); 0x82814 (array
                 g_q + 4 at); 0x82834 (index g_q[at] <= 1023); 0x82844 (array g_cmd + 40 g_q[at]); 0x8289c (index
                 g_nq <= 1023); 0x828b0 (array g_q + 4 g_nq)
     OP6A    1   0x81b70 (signed OW.e3 + 1; OW.e3 = 0 after op_begin's memset of OW)
   41 cursor tests, 6 take tests, 9 table or array index tests, 9 frame address tests, 1 test of g_cmd + 40 serial,
   7 index tests and 1 signed-overflow test: each refuted in its segment by the fact the statement's comment names
   (the input block's bounds and the model's in.n; the image and G addresses below 2 ^ 47 with offsets below 2 ^ 20;
   the class-2 frame's bounds, YCbq.v frames_bounds; serial <= 1024; the model's indices and Some; op_begin). *)

(* ------------------------------------------------------------------ *)
(* 6. The geometry of the core and the transfer every step uses         *)
(* ------------------------------------------------------------------ *)

Section kept. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* A byte array is kept where every one of its bytes is. *)
Lemma lc_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG. apply (garr8_frame segs _ _ _ _ HG). intros a Ha.
apply (mbyte_of_aview segs). replace a with (base + (a - base)) by lia. apply HK. lia.
Qed.

(* What a cut's core and the slot's pre fix about the stack, the frame, the input and the live bytes. *)
Record lc_geo (cx : lcx) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model)
  : Prop := mkLcGeo {
  lg_ar : AR segs B ly' S' W' mem' md';
  lg_sp0al : lc_sp0 cx mod 16 = 0;
  lg_stk : alloc_ceiling <= ly_stk_lo (l_ly cx) /\ ly_stk_lo (l_ly cx) + LLVMF_STK <= lc_sp0 cx /\
           lc_sp0 cx <= ly_stk_hi (l_ly cx) /\ ly_stk_hi (l_ly cx) <= 2 ^ 47;
  lg_sp1 : alloc_ceiling + 32432 <= lc_sp1 cx;
  lg_Faddr : frame_addr ly' LF_CID (l_fpos cx) = lc_F cx;
  lg_Fin : In (LF_CID, l_fpos cx) (frames S');
  lg_n : 0 <= l_n cx < 2 ^ 26 /\ l_n cx = Z.of_nat (length (l_pl cx));
  lg_in : 0 < l_n cx -> In (l_p cx, l_n cx) (ablocks B ly' S');
  lg_live : blocks_bytes S' + LIVE_LIB <= LIVE_MAX
}.

Lemma lc_geom : forall cx ly' S' W' regs' mem' md' e,
  @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e -> lc_geo cx ly' S' W' mem' md'.
Proof.
intros cx ly' S' W' regs' mem' md' e HB HC.
unfold lc_base, tfib_lib_pre_x in HB.
destruct HB as (HAFN & Hra & Ha0 & Ha1 & Hpn & Hnl & Hgp0 & Hfrs0 & Hev & Hlive & Hrod & Hsink & Hfd & Hfss & Hmeta &
  Hmok0).
destruct HAFN as (HAR0 & Hret0 & Hra4 & Hgp' & Htp' & Hstk & Hpres0 & Hch0 & Hqt0).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof HJ as (_ & _ & (memS & HJd & _) & _).
pose proof HJd as (HAR' & _).
apply mkLcGeo.
- exact HAR'.
- exact Hsp0al.
- split; [exact Hceil|]. split; [exact Hslo|]. split; [exact Hshi | exact H47].
- unfold lc_sp0 in *. unfold LLVMF_STK in Hslo. lia.
- unfold lc_F, frame_addr. rewrite HlyF. reflexivity.
- rewrite Hfrs. left. reflexivity.
- split; [destruct Hpn as [[H1 _] | [H1 _]]; lia | exact Hnl].
- intros Hn0. destruct Hpn as [[H1 _] | [_ Hin]]; [lia|].
  exact (Permutation_in _ (Permutation_sym HPERM) Hin).
- rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HPERM), <- (blocks_bytes_bsum B (l_ly cx) (l_S cx)).
  exact Hlive.
Qed.

(* The transfer of lc_core over a stretch of the walk: a run of its own instructions, a call, or both. It asks only
   what lc_core reads: the G journal from the entry at the new state (at FP = [], as lc_core states it), the frames,
   the blocks up to order, the five registers sp, gp, tp, s0 and s1, the 13 saved words [sp0 - 104, sp0) (above the
   spill area: sp1 + 216 <= sp0 - 104), the input's n bytes at p (lc_input), the frame's last word (its flag pointer)
   and the presence of the frame's bytes. A stretch may write the rest of the frame, its shadow, the spill slots, the
   other blocks' bytes and every other register. *)
Lemma lc_core_kept_run : forall cx ly' S' W' regs' mem' md' e ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e2 ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  (forall a, lc_sp0 cx - 104 <= a < lc_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W2) mem2 (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i)) ->
  (forall a, lc_F cx + LF_FBYTES - 8 <= a < lc_F cx + LF_FBYTES ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a -> apresent (w_H W2) mem2 a) ->
  @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 e2.
Proof.
intros cx ly' S' W' regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 e2 HB HC HJ2 HFR2 HP2 HR KS KB KF GA.
pose proof (lc_geom cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof HJ2 as (_ & _ & (memS2 & HJd2 & _) & _).
pose proof HJd2 as (HAR2 & Hly2 & _).
destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
assert (HRi : forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r))
  by exact HR.
split; [exact HJ2|].
split; [rewrite HFR2; exact Hfrs|].
split; [exact EF2|].
split; [exact (Permutation_trans HP2 HPERM)|].
split; [exact (eq_trans (HRi 2 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) Rsp)|].
split; [exact (eq_trans (HRi 8 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R8)|].
split; [exact (eq_trans (HRi 9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R9)|].
split; [exact (eq_trans (HRi 3 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) Rgp)|].
split; [exact (eq_trans (HRi 4 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) Rtp)|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W2) mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; apply KS; lia).
  exact (HSAV o Ho). }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split; [intros a Ha; exact (GA a Ha (HFpres a Ha))|].
split; [rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W2) mem2) (lc_F cx + LF_FBYTES - 8))
          by (intros j Hj; apply KF; lia); exact HFL|].
destruct HIN as (HPAYg & HPAYv).
destruct Hn as (Hn1 & Hnl). split.
- apply (lc_garr8_kept (w_H W') (w_H W2) mem' mem2 (l_p cx) _); [|exact HPAYg].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hnl in Hj. exact (KB j ltac:(lia)).
- intros i Hi. rewrite (KB i Hi). exact (HPAYv i Hi).
Qed.

(* lc_core_kept_run for a call: the callee preserves the callee-saved registers (aregs_preserved) and keeps every byte
   from alloc_ceiling up outside its window [sp1 - X, sp1) (X at most build_and_receive's BAR_STK;
   LLVMFuzzerTestOneInput_cg.v trans_llvmf_use_fits bounds every window by LLVMF_STK - 336), the input's bytes, the
   frame's last word and the presence of the frame's bytes. *)
Lemma lc_core_kept : forall cx ly' S' W' regs' mem' md' e (X : Z) ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e2 ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  aregs_preserved regs' regs2 ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W2) mem2 (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i)) ->
  (forall a, lc_F cx + LF_FBYTES - 8 <= a < lc_F cx + LF_FBYTES ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a -> apresent (w_H W2) mem2 a) ->
  @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 e2.
Proof.
intros cx ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 e2 HB HC HJ2 HFR2 HP2 HPR HX KA KB KF GA.
pose proof (lc_geom cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [_ _ Hstk Hsp1c _ _ _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
change (2 ^ 47) with 140737488355328 in H47. unfold LF_FRAME in Hsp1.
assert (QP : forall r : Z, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r))
  by exact HPR.
apply (lc_core_kept_run cx ly' S' W' regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 e2 HB HC HJ2 HFR2 HP2);
  [| | exact KB | exact KF | exact GA].
- intros r Hr. apply QP. unfold acallee_saved. cbn [In] in Hr. lia.
- intros a Ha. apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia].
Qed.

(* A G journal with no file range (FP = []) is one with the sink token's range [0, 1) as FP: the token only widens
   what the journal allows (aos_step_mono; fp_spares holds at a closed FP), and no clause of the [] journal ever holds
   an address in a range. EXIT gives the post's journal at [sink_token] by this lemma. *)
Lemma lc_fp_token : forall G XO OUT STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G XO OUT STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G XO OUT STK sp0 [sink_token] ly S W mem md own
    ly' S' W' mem' md' k.
Proof.
intros G XO OUT STK sp0 ly S W mem md own ly' S' W' mem' md' k (H0 & H1 & (memS & HJ & Hag) & Hout).
split; [exact H0|]. split; [exact H1|]. split; [exists memS; split; [|exact Hag] | exact Hout].
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Hc; exfalso; exact (sink_closed_nil Hc)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i Hb1 Hb2 Hi _; exact (F2 p n i Hb1 Hb2 Hi (YI04.inFP_nil (p + i)))|].
split; [intros a Hi Ho He _; exact (F3 a Hi Ho He (fp_spares_closed [] a sink_closed_nil))|].
split; [intros cid pos a Hin Hr _; exact (F4 cid pos a Hin Hr (YI04.inFP_nil a))|].
split; [intros p n i Hb1 Hb2 Hi; exfalso; exact (YI04.inFP_nil _ (Hgone p n i Hb1 Hb2 Hi))|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [exact F5 | exact HQT].
Qed.

(* At FP = [] the file descriptors and the file system are the entry's (aos_step_closed at sink_closed_nil): the
   post's fd clause and m_fs md' = ll_fs (LL 0 (m_fs md) []) at EXIT. *)
Lemma lc_journal_io : forall G XO OUT STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G XO OUT STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros G XO OUT STK sp0 ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.

(* The callee-saved registers a cut fixes survive a step that preserves them. *)
Lemma lc_reg_kept : forall (regs' regs2 : bvmap 5 word) (r : Z) (v : word),
  aregs_preserved regs' regs2 -> acallee_saved r ->
  YK11.getr regs' (Z_to_bv 5 r) = v -> YK11.getr regs2 (Z_to_bv 5 r) = v.
Proof. intros regs' regs2 r v HP Hr E. rewrite (HP r Hr). exact E. Qed.

(* The spill slots and the frame's shadow survive a step that keeps the bytes at or above sp1 and the frame's shadow. *)
Lemma lc_spills_kept : forall cx (l : list (Z * Z)) (r r' : reader),
  (forall o, In o l -> 0 <= fst o /\ fst o + 8 <= 216) ->
  (forall a, lc_sp1 cx <= a < lc_sp1 cx + 216 -> r' a = r a) ->
  lc_spills cx l r -> lc_spills cx l r'.
Proof.
intros cx l r r' Hl Hk H. unfold lc_spills in *. rewrite Forall_forall in H |- *. intros o Ho.
rewrite (rdword_ext r r' (lc_sp1 cx + fst o)) by (intros j Hj; apply Hk; pose proof (Hl o Ho); lia).
exact (H o Ho).
Qed.

Lemma lc_fsh_kept : forall cx (r r' : reader) cin bin,
  (forall a, lc_SH cx <= a < lc_SH cx + 32 -> r' a = r a) ->
  lc_fsh cx r cin bin -> lc_fsh cx r' cin bin.
Proof. intros cx r r' cin bin Hk H i Hi. rewrite (Hk (lc_SH cx + i)) by lia. exact (H i Hi). Qed.

End kept.
