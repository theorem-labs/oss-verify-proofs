(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp F_malloc_enf.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RF_enframe RMallocKit_A RMalloc_fp.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
    F fc (m : mem) (st : mstate),
  rw_cells usegs m RCTX (rctx_head_cells st) ->
  rw_cells usegs m RMLOCK [C4 (wz 0)] ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  48 <= bv_unsigned sp ->
  0 <= c_mmap_counter (ctx st) < 2^32 ->
  evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 renframe_entry) fc None m (seg_rom usegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15188) fc None m (seg_rom usegs)).
Proof.
  intros until st. intros CH LK FR SP48 CTR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RCTX, RMLOCK in *. unfold rctx_head_cells, rsecw in CH.
  (* [comment removed for export] *)
  step. Local Ltac2 Set LiaHints.tbl := fun () => "0090>16073343976.471800609155.55 22815487888.4724638473347.5538446806799.5441181558416.4743988483203.5454243526019.5464997134979.5600000500600700800900:00;00<00=S3CTRSSSSSSSS".
rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. step.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x15194)) with (Z_to_bv 64 0x15194) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  do 12 step.
  apply evt_done. unfold renframe_entry. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (o m0 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
    (r : mstate * optr) (ms' : machine_state) : Prop :=
  exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    r = (st', Some p)
    /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
    /\ enf_leaf o st1 g b idx n st' p.

(* [comment removed for export] *)
#[using="Type"] Lemma renf_implT :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
         (o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
  let mr := get_meta_rec st1 g in
  let stride := get_stride mr in
  let ctr := c_mmap_counter (ctx st1) in
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
  mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
  (forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
  0 <= ctr < 2^32 ->
  slot_ok st1 g b r idx n ->
  rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
        (fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 C st1 g b idx n res ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15188) fc None m1 (seg_rom usegs)).
Proof.
  intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
  fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. Local Ltac2 Set LiaHints.tbl := fun () => "00g0?12469719428.11812500199238.12913741138707.12915045277887.11515934513720.87 16100354523.15818431367416.12218575860103.87 18586226854.11420323391847.14720324666399.1292424890845.129 25503110314.12926488659605.15626491150001.12926914067086.11727905103161.15931290091202.12932293188245.1293368247064.129 40587255913.6  40599837782.12941417922635.11742586698327.129446019771.160  48873225672.12949240152210.1295074042873.133 51040968783.12951709126181.15851781418547.12552101693566.15952101693566.16053282644823.11557508919807.12258738108941.15659221393594.1295923435527.118 59850794129.12959882088874.15860596971681.11861929688623.12962198132131.12363369784440.12263401609887.12965099160632.1296533306074.116 65514926510.12365655732996.11866863284536.1226753459898.116 68569559320.1298195563315.9   8528073404.88  8534778781.114 00000100;00H00I00N00`00a00f00k01001501901=01Q01c01d01m02;02@02f03003:03;03?03K04104V04h04i04o05R05g06?06@06A06S06T06X06b07607:07X07\07]07b07g07h07i07j07k07l08608<08A08FSS2E12X22X1S5ATOPR2G02GCSS3IDXS2B02CB2R42SK4FSTrSS3S16S3S16S3S31S3S31S2N0S2X3S5ATOPR4PEND2RC4FSTrS4SPAN5ATOPR2CB2RCSS2LO4FSTrS3CLO2LO5ATOPRS3MPLS2B03S162NS3SCr4SPAN3RI13GI13GI22GR2SKS3IDX4LI32S3IDX4LI32SS2NSS2CB4FSTr2HxS2B03S162NS3SCr4SPAN3RI13GI13GI22GR2SKS2B03S162NS4SPAN2CB3RI13GI13GI22GR2SKS2B03S164SMOD2NS1HFS4FSTrS2B03S164SPAN3RI13GI13GI22GR2SK3OFFS3CLO4PEND2RC4FSTr2HaS3CLO2LO4PEND2RC4FSTr2HaSSS2B02CB2R42SK4FSTrFS2X2S2B02CB2R4S5ATOPR4PEND2RC4FSTrS2X1S2B02N02NS4SPAN5ATOPR2R42RC2SKS2NSSS3CTRS3FBrSSSSSS3IDX4LI32S4SPANS3IDXS3IDX".
apply Z.mul_le_mono_nonneg_l; lia. }
  clear SPAN. rename SPAN1 into SPAN.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  atop_facts.
  (* [comment removed for export] *)
  destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
  pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  atop_facts.
  set (G := conc st1 g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
  set (B := conc st1 b) in *.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  (* [comment removed for export] *)
  pose proof (bytes_at_read usegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read usegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read usegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (* [comment removed for export] *)
  unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
  assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd].
  apply rimplT_rd8. rewrite E3.
  change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
  set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
  set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
  set (off := fold_off off0 slack).
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
  pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
  assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  match goal with |- rimplT _ _ _ ?Q ?ms => 
  assert (GOAL : rimplT o (K off) s Q ms) end.
  2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
      assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
      clearbody off.
      destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
      - rewrite (OFFa E0). exact GOAL.
      - apply rimplT_rd16. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
  subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.
  (* [comment removed for export] *)
  pose proof MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
  eapply evt_cut.
  { eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
      [exact CH| exact LK| exact FR| lia| exact CTR]. }
  intros ms' ->.
  unfold renframe_entry.
  eapply evt_mono.
  { eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
         | |- _ => idtac end.
    all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  split; [reflexivity|].
  fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
  set (res := enframe_at st1 g idx n off) in *.
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - n < 2^31) by lia.
  destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
    as (MRr & TKr & CONCr & FSTr & SNDr).
  fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
  change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
  fold res in MRr, TKr, CONCr, FSTr, SNDr.
  set (P0 := B + 16 + stride * idx) in *.
  rewrite <- EM in MRr.
  destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].
  (* [comment removed for export] *)
  assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
  { rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
    intros x Hx. exact Hx. }
  assert (ST' : stk usegs m' lo (bv_unsigned sp + -48)).
  { eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
  assert (FR' : rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
  release_frame FR' ST' (bv_unsigned sp).
  unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
  split; [reflexivity|].
  split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
  split.
  { rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
    intros x Hx. apply CSL. unfold B in Hx. lia. }
  exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
  split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
