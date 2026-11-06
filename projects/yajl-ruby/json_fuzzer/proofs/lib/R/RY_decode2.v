(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Mem NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RF_strlen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsBits.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_secinst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export RY_decode1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma zbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_sub : forall m A bs i k,
  bytes_at rsegs m A bs -> (i <= length bs)%nat -> bytes_at rsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma bytes_at_zslice : forall m A str i k,
  bytes_at rsegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at rsegs m (A + i) (zbytes (zslice str i k)).
Proof.
  intros m A str i k HB Hi. unfold zslice. rewrite zbytes_firstn, zbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply bytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_skipn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof. intros P str i k HF. unfold zslice. apply Forall_firstn, Forall_skipn. exact HF. Qed.

(* [comment removed for export] *)
Lemma yzext32_idiom : forall x, 0 <= x < 2^32 ->
  (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 32)) ≫ 32) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2^64) with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma yswrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite ybv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)
End RC__1.
Open Scope yprog_scope.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YAP : ybuf_append_stmt HK.
Hypothesis YHX : yhexToDigit_stmt.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_of_Z by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lkr := repeat match goal with H : LKnil ?l |- _ => unfold LKnil in H end; rewrite ?app_nil_r; repeat match goal with H : ?l = [] |- context [?l] => rewrite H end; cbn [app].
Ltac lk0 := lkr; reflexivity.
(* [comment removed for export] *)
Ltac sb_store := unfold wz; rewrite le1_wz by lia; mem_after_store.
Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Section Fn.
Variables (REST : list block) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n lo B : Z) (errv : word) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState)
    (db' : ybuf) (mbd' : mbuf) (LK : list block),
  ystring_decode_rpost HK sp tp m REST mbd db AF S str n lo B errv a0' m' mo' s' db' mbd' LK ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = wz RATP.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RY_DECODE_STACK.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis AFIN : yaf_in REST AF.
Hypothesis YR : yroom REST 3.
Hypothesis SF : Forall (fun c => 0 <= c < 256) str.
Hypothesis NL : n = zlength str.
Hypothesis N26 : n < 2^26.
Hypothesis SNZ : S <> 0.
Hypothesis S62 : S + n < 2^62.
Hypothesis TR : (exists bt, In bt REST /\ blk_addr bt <= S /\ S + n <= blk_addr bt + blk_size bt) \/ n = 0.
Hypothesis STXT : 0 < n -> S + n <= alloc_ceiling.
Hypothesis AFC : AF + 32 <= alloc_ceiling.

(* [comment removed for export] *)
#[local] Definition dlits := ltac2:(inst_sec '@RY_decode1.dlits).
#[local] Definition dframe := ltac2:(inst_sec '@RY_decode1.dframe).
#[local] Definition str_pres_munch := ltac2:(inst_sec '@RY_decode1.str_pres_munch).
#[local] Definition dsaved := ltac2:(inst_sec '@RY_decode1.dsaved).
Let WHOLE := ydecode_loop (decode_fuel n) db str n 0 0.
#[local] Definition head_ok := ltac2:(inst_sec '@RY_decode1.head_ok).
#[local] Definition decode_lit := ltac2:(inst_sec '@RY_decode1.decode_lit).
#[local] Definition dframe_join := ltac2:(inst_sec '@RY_decode1.dframe_join).
#[local] Definition utf8_bytes := ltac2:(inst_sec '@RY_decode1.utf8_bytes).
#[local] Definition decode_u8 := ltac2:(inst_sec '@RY_decode1.decode_u8).
#[local] Definition dframe_split := ltac2:(inst_sec '@RY_decode1.dframe_split).
#[local] Definition decode_cp := ltac2:(inst_sec '@RY_decode1.decode_cp).
Ltac after_u8 OWNU MU WM F1 F2 F3 :=
  let X := fresh "OW" in pose proof (OWNU _ MU WM) as X;
  destruct X as ([HK2 AX2] & YS2 & PRES2 & BR2 & TB2);
  lazymatch goal with F4' : rw_cells _ ?mx (bv_unsigned _ + -112) (CB 3 ?padx :: C1 ?v0 :: C1 ?v1 :: C1 ?v2 :: C1 ?v3 :: C1 ?v4 :: _) |- _ =>
    pose proof (dframe_join mx _ _ _ padx v0 v1 v2 v3 v4 ltac:(exact F1) ltac:(exact F2) ltac:(exact F3) F4') as FRJ;
    pose proof (utf8_bytes mx padx v0 v1 v2 v3 v4 F4') as UB; cbn [app] in UB end.


(* [comment removed for export] *)
Lemma str_read : forall mx i, bytes_at rsegs mx S (zbytes str) -> 0 <= i < n ->
  ov_read_bytes rsegs mx (wa (S + i)) 1 = Some [Z_to_bv 8 (znth str i)].
Proof. intros mx i TB Hi. eapply (u8ro_read rsegs); [exact TB| apply zbytes_nth; lia| lia| reflexivity]. Qed.

Lemma str_byte : forall i, 0 <= i < n -> 0 <= znth str i < 256.
Proof.
  intros i Hi. unfold znth. destruct (Z.ltb_spec i 0); [lia|]. rewrite Forall_forall in SF.
  destruct (nth_error str (Z.to_nat i)) eqn:E; [| apply nth_error_None in E; unfold zlength in NL; lia].
  rewrite (nth_error_nth _ _ _ E). apply SF. eapply nth_error_In. exact E.
Qed.

(* [comment removed for export] *)
Lemma decode_4 : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v s6v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b1 : ybuf) (mb1 : mbuf) (LK : list block) (p cp : Z)
    (j0 : list byte) (surw cpw : word) (pad : list byte) (w0 w1 w2 w3 w4 : byte),
  LK = [] -> HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells rsegs m1 (bv_unsigned sp + -208) (CB 8 j0 :: dlits) ->
  rw_cells rsegs m1 (bv_unsigned sp + -120) [C4 surw] -> rw_cells rsegs m1 (bv_unsigned sp + -116) [C4 cpw] ->
  rw_cells rsegs m1 (bv_unsigned sp + -112) (CB 3 pad :: C1 w0 :: C1 w1 :: C1 w2 :: C1 w3 :: C1 w4 :: dsaved) ->
  stk rsegs m1 lo (bv_unsigned sp + -208) -> mem_inv rsegs m1 -> rauxv_ok m1 B ->
  rw_cells rsegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells rsegs m1 AF (alloc_cells ryc) ->
  bytes_at rsegs m1 S (zbytes str) ->
  buf_rep rsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  65536 <= cp < 2097152 ->
  yb_used b1 + 4 <= p + 1 -> 0 <= p -> p + 1 <= n -> sbody_ix str (p + 1) n -> (Z.to_nat (n - p) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 (u8enc cp) ;; ydecode_loop f' b2 str n (p + 1) (p + 1)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb1)) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz n) s3v (wz 113) (wz cp) s6v (wz 64512) (wz p) (wz 92) (wz 101) (wz 91) t3 t4 t5 t6)
                           F (wz 0x16bb4) fc None m1 (seg_rom rsegs)) mo1) K.
Proof.
  intros f' HEAD. intros until w4. intros ELK HK1 YS1 F1 F2 F3 F4 STK MI AX ERR PRES YAF TB BR BI MBS CPR HUSED P0 PN SBP HF HL. apply lk_hide in ELK.
  unfold dsaved, RY_decode1.dsaved, wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RERRNO in ERR.
  pose proof AFC as AFC'. unfold alloc_ceiling in AFC'. unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF.
  unfold dlits, RY_decode1.dlits in F1.
  pose proof (proj1 (proj1 F4)) as WF4. cbn [cells_wf cell_wf] in WF4. destruct WF4 as (LP & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  destruct AFIN as (hb & HBI & HB1 & HB2).
  pose proof (munch_refl [(bv_unsigned sp + -109, bv_unsigned sp + -104)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  assert (OWNU : forall mx, munch [(bv_unsigned sp + -109, bv_unsigned sp + -104)] m1 mx -> wmono rsegs m1 mx ->
            (HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) mx mo1 /\ rauxv_ok mx B) /\ ystatics mx /\ ry_pres REST (bv_unsigned sp) [] m mx
            /\ buf_rep rsegs mx mb1 b1 AF /\ bytes_at rsegs mx S (zbytes str)).
  { intros mx MU1 WM1. split; [| split; [| split; [| split]]].
    - eapply (yown_writes HK HKF); [exact HK1| exact AX| exact MU1| exact WM1| |].
      + constructor; [left; cbn; unfold alloc_ceiling; lia| constructor].
      + constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
    - eapply ystatics_munch; [exact YS1| exact MU1| exact WM1|]. constructor; [cbn; unfold RY_CALLBACKS; lia| constructor].
    - eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU1| exact WM1|].
      intros a Ha Hc _. cbn. split; [| exact I].
      destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ (proj1 (HK_blocks HK HKB _ _ _ _ HK1)) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)) as Hbr.
      unfold rblock_range, alloc_ceiling in Hbr. lia.
    - eapply (buf_rep_transport_hi _ _ _ _ _ _ _ BR MU1 WM1); [exact (proj1 (HK_blocks HK HKB _ _ _ _ HK1))| intros bq Hq; apply in_or_app; left; exact Hq|].
      constructor; [cbn; unfold alloc_ceiling; lia| constructor].
    - eapply str_pres_munch; [exact MU1| | exact TB]. constructor; [cbn; unfold alloc_ceiling; lia| constructor]. }
  yhide TB. clear PRES BR.
  destruct (u8enc_4 cp ltac:(lia)) as (UE & R0 & R1 & R2 & R3).
  pose proof (shiftr_range cp 18 21 ltac:(lia) ltac:(lia)) as SR18. change (2 ^ (21 - 18)) with 8 in SR18.
  rz_seg HKS HK1.
  step. step. step. step. step. step. step. step. step. step.
  rewrite !(unsigned_lit cp) by lia. rewrite (unsigned_lit (cp ≫ 18)) by lia. rewrite yfield12 by lia. rewrite yfield6 by lia. rewrite lead4 by lia.
  step. sb_store. step. sb_store. step. sb_store. step. sb_store. step. step.
  apply evt_done. after_u8 OWNU MU WM F1 F2 F3.
  lazymatch goal with F4' : rw_cells _ ?mx (bv_unsigned _ + -112) _ |- _ =>
  eapply (decode_u8 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx mo1 s1' errv1 b1 mb1 LK p
            [Z.shiftr cp 18 + 240; Z.land (Z.shiftr cp 12) 63 + 128; Z.land (Z.shiftr cp 6) 63 + 128; Z.land cp 63 + 128] j0 surw cpw pad _ []);
    [ lk0 | exact HK2 | exact YS2 | exact F1 | exact F2 | exact F3 | cbn [zbytes map app]; exact F4' | reflexivity
    | assumption | assumption | exact AX2 | assumption | exact PRES2 | exact YAF | exact TB2 | exact BR2 | exact BI | exact MBS
    | repeat constructor; lia | clear; cbn; lia | unfold wz, zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; f_equal; lia
    | unfold zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact PN | exact SBP | exact HF
    | rewrite <- UE; exact HL ] end.
Qed.

(* [comment removed for export] *)
Lemma decode_uesc : forall f', head_ok f' ->
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b b1 : ybuf) (mb1 : mbuf) (LK : list block) (beg e : Z) (j0 j88 : list byte),
  LK = [] -> HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells rsegs m1 (bv_unsigned sp + -208) (dframe j0 j88) -> stk rsegs m1 lo (bv_unsigned sp + -208) -> mem_inv rsegs m1 -> rauxv_ok m1 B ->
  rw_cells rsegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells rsegs m1 AF (alloc_cells ryc) ->
  bytes_at rsegs m1 S (zbytes str) ->
  buf_rep rsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 -> yb_used b1 <= e ->
  0 <= beg <= e -> e + 5 < n -> znth str e = c_bslash -> znth str (e + 1) = c_u ->
  (forall k, 0 <= k < 4 -> is_vhc (znth str (e + 2 + k)) = true) -> sbody_ix str (e + 6) n ->
  (Z.to_nat (n - e) < Datatypes.S f')%nat ->
  yleaf (ybuf_append b (zslice str beg (e - beg))) b1 ->
  (forall r, yleaf (ydecode_loop (Datatypes.S f') b str n beg e) r -> yleaf WHOLE r) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR (wz 92600) (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb1)) (wz S) (wz 117) a1 a2 a3 a4 a5 a6 a7 (wz n) s3v (wz 113) (wz 34) (wz e) (wz 64512) (wz (e + 1)) (wz 92) (wz 101) (wz 91) t3 t4 t5 t6)
                           F (wz 0x169ec) fc None m1 (seg_rom rsegs)) mo1) K.
Proof.
  intros f' HEAD. intros until j88. intros ELK HK1 YS1 FR STK MI AX ERR PRES YAF TB BR BI MBS UB HBE E5 CB CU HHEX HREST HF HLB1 HL. apply lk_hide in ELK.
  unfold wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RERRNO in ERR.
  pose proof AFC as AFC'. unfold alloc_ceiling in AFC'. unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF.
  pose proof (zlength_nonneg str) as NL0. pose proof (proj1 TB) as S0.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  destruct (dframe_split _ _ _ FR) as (pad & w0 & w1 & w2 & w3 & w4 & F1 & F2 & F3 & F4). clear FR. unfold dlits, RY_decode1.dlits in F1. unfold dsaved, RY_decode1.dsaved in F4.
  (* [comment removed for export] *)
  destruct (yhexToDigit_bound str (e + 2) HHEX) as (cp & HX & CPR). pose proof HX as HXL. unfold yhexToDigit in HXL.
  pose proof (bytes_at_zslice m1 S str (e + 2) 4 TB ltac:(lia)) as HB4. rewrite zslice4 in HB4 by lia.
  replace (e + 2 + 1) with (e + 3) in * by lia. replace (e + 2 + 2) with (e + 4) in * by lia. replace (e + 2 + 3) with (e + 5) in * by lia.
  assert (SN : S + n <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)) by (apply STXT; lia).
  cbn [zbytes map] in HB4.
  pose proof (munch_refl [(lo, bv_unsigned sp + -208); (bv_unsigned sp + -120, bv_unsigned sp + -104)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  yhide TB.
  rz_seg HKS HK1.
  step. lit_store. step. step. step. rewrite (yzext32_idiom (e + 2)) by lia. step. step.
  step. call (YHX (bv_unsigned sp + -116) (S + (e + 2)) 0 lo (znth str (e + 2)) (znth str (e + 3)) (znth str (e + 4)) (znth str (e + 5)) cp).
  all: try exact F3. 1:{ clear; lia. } 1:{ exact HB4. }
  1:{ replace (e + 2) with (e + 2 + 0) by lia. apply HHEX. clear; lia. } 1:{ replace (e + 3) with (e + 2 + 1) by lia. apply HHEX. clear; lia. }
  1:{ replace (e + 4) with (e + 2 + 2) by lia. apply HHEX. clear; lia. } 1:{ replace (e + 5) with (e + 2 + 3) by lia. apply HHEX. clear; lia. }
  1:{ exact HXL. } 1:{ left. lia. } 1:{ rewrite ESP. assumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ left. lia. }
  1:{ assumption. } 1:{ reflexivity. } 1:{ reflexivity. }
  (* [comment removed for export] *)
  apply evt_done.
  lazymatch goal with X : stk rsegs ?mx lo _ |- _ => rename X into STK2; rename mx into m2 end.
  lazymatch goal with X : mem_inv rsegs m2 |- _ => rename X into MI2 end.
  lazymatch goal with X : rw_cells rsegs m2 (bv_unsigned sp + -116) _ |- _ => rename X into F3 end.
  rewrite ESP in STK2. clear HB4. try (lazymatch goal with X : bytes_at rsegs m2 (S + (e + 2)) _ |- _ => clear X end).
  assert (WOK : Forall (rclient_write_ok (buf_blocks mb1 b1 ++ LK ++ REST)) [(lo, bv_unsigned sp + -208); (bv_unsigned sp + -120, bv_unsigned sp + -104)]).
  { constructor; [left; cbn; unfold alloc_ceiling; lia|]. constructor; [left; cbn; unfold alloc_ceiling; lia| constructor]. }
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK1 AX MU WM WOK
              ltac:(constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor])) as [HK2 AX2].
  pose proof (ystatics_munch _ _ _ YS1 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia|]; constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS2.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _.
    assert (Hlo : bv_unsigned sp <= a \/ a < lo).
    { destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ (proj1 (HK_blocks HK HKB _ _ _ _ HK1)) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)) as Hbr.
      unfold rblock_range, alloc_ceiling in Hbr. lia. }
    cbn. split; [lia|]. split; [lia| exact I]. }
  assert (BR2 : buf_rep rsegs m2 mb1 b1 AF).
  { eapply (buf_rep_transport_hi _ _ _ _ _ _ _ BR MU WM); [exact (proj1 (HK_blocks HK HKB _ _ _ _ HK1))| intros bq Hq; apply in_or_app; left; exact Hq|].
    constructor; [cbn; unfold alloc_ceiling; lia|]. constructor; [cbn; unfold alloc_ceiling; lia| constructor]. }
  yshow TB. pose proof (str_pres_munch _ _ _ MU ltac:(constructor; [cbn; unfold alloc_ceiling; lia|]; constructor; [cbn; unfold alloc_ceiling; lia| constructor]) TB) as TB2.
  clear TB MU WM HK1 YS1 AX PRES BR. try clear MI. try clear STK.
  (* [comment removed for export] *)
  assert (QLIT : forall (rav q0 q1 q2 a0x a1x a2x a3x a4x a5x a6x a7x s5x q3 q4 q5 q6 : word),
    Z.land cp 64512 = 55296 ->
    (e + 1 + 1 + 3 + 2 <? n) && (znth str (e + 1 + 1 + 3 + 1) =? c_bslash) && (znth str (e + 1 + 1 + 3 + 2) =? c_u) = false ->
    realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -208)) gp tp q0 q1 q2 (Z_to_bv 64 (mb_addr mb1)) (Z_to_bv 64 S)
          a0x a1x a2x a3x a4x a5x a6x a7x (Z_to_bv 64 n) (Z_to_bv 64 66328) (Z_to_bv 64 113) s5x (Z_to_bv 64 e) (Z_to_bv 64 64512) (Z_to_bv 64 (e + 5))
          (Z_to_bv 64 92) (Z_to_bv 64 101) (Z_to_bv 64 91) q3 q4 q5 q6) F (Z_to_bv 64 0x16c08) fc None m2 (seg_rom rsegs)) mo1) K).
  { intros until q6. intros HS HLOOK.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    rz_seg HKS HK2. step. apply evt_done.
    pose proof (dframe_join m2 _ _ _ pad w0 w1 w2 w3 w4 ltac:(exact F1) ltac:(exact F2) ltac:(exact F3) F4) as FRJ.
    eapply (decode_lit f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo1 s1' errv1 b1 mb1 LK (e + 5) 66328 [63] [121; 97; 106; 108; 95; 98] j0 _);
      [ lk0 | exact HK2 | exact YS2 | exact FRJ | exact STK2 | exact MI2 | exact AX2 | exact ERR | exact PRES2 | exact YAF | exact TB2
      | exact BR2 | exact BI | exact MBS
      | apply lit_bytes; [exact MI2| vm_compute; reflexivity| zle| zle]
      | forall_bytes | intros [X|[]]; lia | clear; cbn; lia | zle | discriminate
      | left; split; zle
      | unfold zlength; cbn [length]; lia | lia | lia | replace (e + 5 + 1) with (e + 6) by lia; exact HREST | lia | ].
    intros r Hr. apply HL. eapply (dlf_uq f' b str n beg e cp b1 r); [lia| exact CB| exact CU| replace (e + 1 + 1) with (e + 2) by lia; exact HX| exact HS| exact HLOOK| exact HLB1|].
    replace (e + 1 + 1 + 3 + 1) with (e + 5 + 1) by lia. exact Hr. }
  pose proof (land_lt16 cp ltac:(lia)) as LA.
  pose proof (munch_refl [(lo, bv_unsigned sp + -208); (bv_unsigned sp + -120, bv_unsigned sp + -104)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
  rz_seg HKS HK2.
  step. rewrite yzx32_small by lia.
  step. step. step. rewrite (unsigned_lit cp) by lia.
  step. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    assert (HNS : Z.land cp 64512 <> 55296) by (revert K1; unfold wz; rewrite ?unsigned_lit by lia; intros K1; lia).
    apply evt_done.
    eapply (decode_cp f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo1 s1' errv1 b1 mb1 LK e (e + 5) cp j0 _ pad w0 w1 w2 w3 w4);
      [ lk0 | exact HK2 | exact YS2 | exact F1 | exact F2 | exact F3 | exact F4 | exact STK2 | exact MI2 | exact AX2 | exact ERR | exact PRES2 | exact YAF | exact TB2
      | exact BR2 | exact BI | exact MBS | exact CPR | reflexivity | lia | lia | lia | replace (e + 5 + 1) with (e + 6) by lia; exact HREST | lia | ].
    intros r Hr. apply HL. eapply (dlf_u f' b str n beg e cp b1 r); [lia| exact CB| exact CU| replace (e + 1 + 1) with (e + 2) by lia; exact HX| exact HNS| exact HLB1|].
    replace (e + 1 + 1 + 3 + 1) with (e + 5 + 1) by lia. unfold u8enc in Hr. exact Hr.
  - (* [comment removed for export] *)
    assert (HS : Z.land cp 64512 = 55296) by (revert K1; unfold wz; rewrite ?unsigned_lit by lia; intros K1; lia).
    step. rewrite (unsigned_lit e) by lia. rewrite yswrap32_small by lia.
    step. step.
    step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      apply evt_done. apply QLIT; [exact HS|]. apply andb_false_intro1. apply andb_false_intro1. apply Z.ltb_ge.
      revert K2; rewrite ?unsigned_lit by lia; intros K2; lia.
    + assert (E7 : e + 7 < n) by (revert K2; rewrite ?unsigned_lit by lia; intros K2; lia).
      pose proof (str_byte (e + 6) ltac:(lia)) as C6.
      pose proof (str_read m2 (e + 6) TB2 ltac:(lia)) as RD.
      step. step. step. rewrite (yzext32_idiom (e + 6)) by lia. step. step. clear RD.
      unfold zxb. rewrite (Z_to_bv_small 8 (znth str (e + 6))) by (unfold bv_modulus; lia).
      step. if_cases K3; zify_cond K3.
      * apply evt_done. apply QLIT; [exact HS|]. apply andb_false_intro1. apply andb_false_intro2. apply Z.eqb_neq.
        replace (e + 1 + 1 + 3 + 1) with (e + 6) by lia. unfold c_bslash. revert K3; rewrite ?unsigned_lit by lia; intros K3; lia.
      * pose proof (str_byte (e + 7) ltac:(lia)) as C7.
        pose proof (str_read m2 (e + 7) TB2 ltac:(lia)) as RD.
        step. step. rewrite (yzext32_idiom (e + 7)) by lia. step. step. clear RD.
        unfold zxb. rewrite (Z_to_bv_small 8 (znth str (e + 7))) by (unfold bv_modulus; lia).
        step. step. if_cases K4; zify_cond K4.
        -- apply evt_done. apply QLIT; [exact HS|]. apply andb_false_intro2. apply Z.eqb_neq.
           replace (e + 1 + 1 + 3 + 2) with (e + 7) by lia. unfold c_u. revert K4; rewrite ?unsigned_lit by lia; intros K4; lia.
        -- (* [comment removed for export] *)
           assert (CB2 : znth str (e + 6) = c_bslash) by (unfold c_bslash; revert K3; rewrite ?unsigned_lit by lia; intros K3; lia).
           assert (CU2 : znth str (e + 7) = c_u) by (unfold c_u; revert K4; rewrite ?unsigned_lit by lia; intros K4; lia).
           assert (LX2 : e + 11 < n /\ (forall k, 0 <= k < 4 -> is_vhc (znth str (e + 8 + k)) = true) /\ sbody_ix str (e + 12) n).
           { inversion HREST as [| i j Hlt Hnb Hrest| i j Hlt Hb Hvec Hrest| i j Hlt Hb Hu Hhex Hrest]; subst; [lia| congruence| |].
             - exfalso. replace (e + 6 + 1) with (e + 7) in Hvec by lia. rewrite CU2 in Hvec. revert Hvec. clear. vm_compute. discriminate.
             - split; [lia|]. split; [intros k Hk; replace (e + 8 + k) with (e + 6 + 2 + k) by lia; apply Hhex; lia| replace (e + 12) with (e + 6 + 6) by lia; exact Hrest]. }
           destruct LX2 as (E11 & HHEX2 & HREST2).
           destruct (yhexToDigit_bound str (e + 8) HHEX2) as (sur & HX2 & SURR). pose proof HX2 as HXL2. unfold yhexToDigit in HXL2.
           pose proof (bytes_at_zslice m2 S str (e + 8) 4 TB2 ltac:(lia)) as HB8. rewrite zslice4 in HB8 by lia.
           replace (e + 8 + 1) with (e + 9) in HXL2, HB8 by lia. replace (e + 8 + 2) with (e + 10) in HXL2, HB8 by lia. replace (e + 8 + 3) with (e + 11) in HXL2, HB8 by lia.
           cbn [zbytes map] in HB8.
           yhide TB2.
           step. lit_store. step. step.
           step. call (YHX (bv_unsigned sp + -120) (S + (e + 8)) 0 lo (znth str (e + 8)) (znth str (e + 9)) (znth str (e + 10)) (znth str (e + 11)) sur).
           all: try exact F2. 1:{ clear; lia. } 1:{ exact HB8. }
           1:{ replace (e + 8) with (e + 8 + 0) by lia. apply HHEX2. clear; lia. } 1:{ replace (e + 9) with (e + 8 + 1) by lia. apply HHEX2. clear; lia. }
           1:{ replace (e + 10) with (e + 8 + 2) by lia. apply HHEX2. clear; lia. } 1:{ replace (e + 11) with (e + 8 + 3) by lia. apply HHEX2. clear; lia. }
           1:{ exact HXL2. } 1:{ left. lia. } 1:{ rewrite ESP. assumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ left. lia. }
           1:{ assumption. } 1:{ unfold wz; f_equal; lia. } 1:{ unfold wz; f_equal; lia. }
           (* [comment removed for export] *)
           step. rewrite yzx32_small by lia.
           step. step. step. step. step. step. step.
           assert (SL : 0 <= cp ≪ 10 < 67108864) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
           pose proof (land_lt_pow2 (cp ≪ 10) 1047552 20 ltac:(lia) ltac:(lia) ltac:(lia)) as LB1.
           pose proof (land_lt_pow2 sur 1023 10 ltac:(lia) ltac:(lia) ltac:(lia)) as LB2.
           unfold wz. rewrite !(unsigned_lit cp), !(unsigned_lit sur), !(unsigned_lit 1047552) by lia.
           rewrite !(unsigned_lit (cp ≪ 10)) by lia. rewrite !(unsigned_lit (Z.land (cp ≪ 10) 1047552)) by lia. rewrite !(unsigned_lit (Z.land sur 1023)) by lia.
           assert (CSR : 65536 <= combine_surrogate cp sur < 2097152).
           { pose proof (combine_surrogate_bound cp sur ltac:(lia) ltac:(lia)) as CB0.
             rewrite <- (combine_surrogate_machine cp sur) in CB0 by lia. rewrite <- (combine_surrogate_machine cp sur) by lia.
             pose proof (proj2 (Z.lor_nonneg (Z.land (Z.shiftl cp 10) 1047552) (Z.land sur 1023)) (conj (proj1 LB1) (proj1 LB2))). lia. }
           rewrite (combine_surrogate_machine cp sur) by lia.
           step. step. step. apply evt_done.
           (* [comment removed for export] *)
           lazymatch goal with X : munch _ m2 ?mx |- _ => rename mx into m3 end.
           lazymatch goal with X : stk rsegs m3 lo _ |- _ => rename X into STK3 end. rewrite ESP in STK3.
           lazymatch goal with X : mem_inv rsegs m3 |- _ => rename X into MI3 end.
           lazymatch goal with X : rw_cells rsegs m3 (bv_unsigned sp + -116) _ |- _ => rename X into F3' end.
           lazymatch goal with X : rw_cells rsegs m3 (bv_unsigned sp + -120) _ |- _ => rename X into F2' end.
           destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2 AX2 MU WM WOK
                       ltac:(constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor])) as [HK3 AX3].
           pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia|]; constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS3.
           assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m3).
           { eapply ry_pres_trans; [exact PRES2|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
             intros a Ha Hc _.
             assert (Hlo : bv_unsigned sp <= a \/ a < lo).
             { destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
               pose proof (all_range_In _ _ (proj1 (HK_blocks HK HKB _ _ _ _ HK2)) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)) as Hbr.
               unfold rblock_range, alloc_ceiling in Hbr. lia. }
             cbn. split; [lia|]. split; [lia| exact I]. }
           assert (BR3 : buf_rep rsegs m3 mb1 b1 AF).
           { eapply (buf_rep_transport_hi _ _ _ _ _ _ _ BR2 MU WM); [exact (proj1 (HK_blocks HK HKB _ _ _ _ HK2))| intros bq Hq; apply in_or_app; left; exact Hq|].
             constructor; [cbn; unfold alloc_ceiling; lia|]. constructor; [cbn; unfold alloc_ceiling; lia| constructor]. }
           yshow TB2. pose proof (str_pres_munch _ _ _ MU ltac:(constructor; [cbn; unfold alloc_ceiling; lia|]; constructor; [cbn; unfold alloc_ceiling; lia| constructor]) TB2) as TB3.
           eapply (decode_4 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo1 s1' errv1 b1 mb1 LK (e + 11) (combine_surrogate cp sur) j0 _ _ pad w0 w1 w2 w3 w4);
             [ lk0 | exact HK3 | exact YS3 | exact F1 | exact F2' | exact F3' | exact F4 | exact STK3 | exact MI3 | exact AX3 | exact ERR | exact PRES3 | exact YAF | exact TB3
             | exact BR3 | exact BI | exact MBS | exact CSR | lia | lia | lia | replace (e + 11 + 1) with (e + 12) by lia; exact HREST2 | lia | ].
           intros r Hr. apply HL.
           eapply (dlf_us f' b str n beg e cp sur b1 r);
             [ lia | exact CB | exact CU | replace (e + 1 + 1) with (e + 2) by lia; exact HX | exact HS | lia
             | replace (e + 1 + 1 + 3 + 1) with (e + 6) by lia; exact CB2 | replace (e + 1 + 1 + 3 + 2) with (e + 7) by lia; exact CU2
             | replace (e + 1 + 1 + 3 + 1 + 2) with (e + 8) by lia; exact HX2 | exact HLB1 | ].
           replace (e + 1 + 1 + 3 + 1 + 5 + 1) with (e + 11 + 1) by lia. unfold u8enc in Hr. exact Hr.
Qed.
End Fn.
End S.
End RC__2.
