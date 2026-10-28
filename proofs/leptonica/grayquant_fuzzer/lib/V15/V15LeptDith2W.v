(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom DitherLib DitherLoop DitherTab DitherTabLoop KernelW KernelW2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopy V15Dith2Low V15LeptDith2 V15LeptDith2Low.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition D2K_CLOB : list reg := [1; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 19; 23; 24; 26; 27; 28; 29; 30; 31]%bv.

Section Dith2W.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma dith_wpl_facts2 : forall w h, hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  (1 <= wpl_of w 8 <= 5000 /\ 1 <= wpl_of w 2 <= 1250 /\ w <= 4 * wpl_of w 8 /\ w <= 16 * wpl_of w 2 /\ wpl_of w 2 <= wpl_of w 8 /\
   wpl_of w 8 * h <= 2 ^ 24 /\ wpl_of w 2 * h <= 2 ^ 24 /\ 1 <= wpl_of w 8 * h /\ 1 <= wpl_of w 2 * h)%Z.
Proof.
  intros w h (DV & Hw & Hh & Hsz) Hw1 Hh1. unfold wpl_of in *.
  pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)) as M8.
  pose proof (Z.div_mod (w * 2 + 31) 32 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (w * 2 + 31) 32 ltac:(lia)) as M2.
  set (a := ((w * 8 + 31) / 32)%Z) in *. set (b := ((w * 2 + 31) / 32)%Z) in *.
  assert (Hba : (b <= a)%Z) by lia. assert (Hb1 : (1 <= b)%Z) by lia. assert (Ha1 : (1 <= a)%Z) by lia.
  pose proof (Z.mul_le_mono_nonneg_r b a h ltac:(lia) Hba) as P1.
  pose proof (Z.mul_le_mono_nonneg 1 a 1 h ltac:(lia) Ha1 ltac:(lia) Hh1) as P2.
  pose proof (Z.mul_le_mono_nonneg 1 b 1 h ltac:(lia) Hb1 ltac:(lia) Hh1) as P3.
  repeat split; lia.
Qed.
Lemma hdr_ok_8_2 : forall w h, hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h 2.
Proof.
  intros w h HOK Hw Hh. destruct (dith_wpl_facts2 w h HOK Hw Hh) as (_ & _ & _ & _ & _ & _ & P1 & _). destruct HOK as (_ & X & Y & _).
  split; [unfold dval; tauto|]. split; [exact X|]. split; [exact Y|]. lia.
Qed.

Theorem d2k_hop_W : forall (fx : FPState) C A Ar M md regs (s w h datad datat bufs1 bufs2 tabval tab38 tab14 : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 512 <= s)%Z -> (s <= c_top C)%Z ->
  hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 2 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datat) = Some (4 * (wpl_of w 8 * h))%Z ->
  live A (Z_to_bv 64 bufs1) = Some (4 * wpl_of w 8)%Z -> live Ar (Z_to_bv 64 bufs1) = None -> live (c_A0 C) (Z_to_bv 64 bufs1) = None ->
  live A (Z_to_bv 64 bufs2) = Some (4 * wpl_of w 8)%Z -> live Ar (Z_to_bv 64 bufs2) = None -> live (c_A0 C) (Z_to_bv 64 bufs2) = None ->
  live A (Z_to_bv 64 tabval) = Some (1024)%Z -> live Ar (Z_to_bv 64 tabval) = None -> live (c_A0 C) (Z_to_bv 64 tabval) = None ->
  live A (Z_to_bv 64 tab38) = Some (1024)%Z -> live Ar (Z_to_bv 64 tab38) = None -> live (c_A0 C) (Z_to_bv 64 tab38) = None ->
  live A (Z_to_bv 64 tab14) = Some (1024)%Z -> live Ar (Z_to_bv 64 tab14) = None -> live (c_A0 C) (Z_to_bv 64 tab14) = None ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datat < 2 ^ 64)%Z -> (0 <= bufs1 < 2 ^ 64)%Z -> (0 <= bufs2 < 2 ^ 64)%Z -> (0 <= tabval < 2 ^ 64)%Z -> (0 <= tab38 < 2 ^ 64)%Z -> (0 <= tab14 < 2 ^ 64)%Z ->
  List.NoDup [Z_to_bv 64 datad; Z_to_bv 64 datat; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] ->
  (forall i, (0 <= i < 1024)%Z -> M (at_ (Z_to_bv 64 tab38) i) = Some (Z_to_bv 8 0)) ->
  (forall i, (0 <= i < 1024)%Z -> M (at_ (Z_to_bv 64 tab14) i) = Some (Z_to_bv 8 0)) ->
  getr regs 2 = Z_to_bv 64 (s + -208) -> getr regs 9 = Z_to_bv 64 bufs1 -> getr regs 18 = Z_to_bv 64 bufs2 -> getr regs 20 = Z_to_bv 64 tabval -> getr regs 21 = Z_to_bv 64 tab38 -> getr regs 22 = Z_to_bv 64 tab14 -> getr regs 25 = Z_to_bv 64 datad ->
  rdn SEGS M (Z_to_bv 64 (s + -108)) 4 = Some (Z_to_le_bytes 4 (w)) ->
  rdn SEGS M (Z_to_bv 64 (s + -112)) 4 = Some (Z_to_le_bytes 4 (h)) ->
  rdn SEGS M (Z_to_bv 64 (s + -152)) 8 = Some (Z_to_le_bytes 8 (wpl_of w 8)) ->
  rdn SEGS M (Z_to_bv 64 (s + -160)) 8 = Some (Z_to_le_bytes 8 (datat)) ->
  rdn SEGS M (Z_to_bv 64 (s + -168)) 8 = Some (Z_to_le_bytes 8 (wpl_of w 2)) ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> regs_agree (fun r => In r D2K_CLOB) regs regs' -> 
      (forall a : word, (s + -208 <= u a < s + -200)%Z \/ (s + -184 <= u a < s + -176)%Z \/ (s + -168 <= u a < s + 0)%Z -> m' a = M a) ->
      (forall (q : word) k, live A q = Some k -> ~ List.In q [Z_to_bv 64 datad; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] -> forall i, (0 <= i < k)%Z -> m' (at_ q i) = M (at_ q i)) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 118356) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 116832) M al_rom) md) S.
Proof.
  intros fx C A Ar M md regs s w h datad datat bufs1 bufs2 tabval tab38 tab14 S CK HW SUB Hs16 Hlo Hhi HOK Hw1 Hh1 Ldatad Fdatad F0datad Ldatat Lbufs1 Fbufs1 F0bufs1 Lbufs2 Fbufs2 F0bufs2 Ltabval Ftabval F0tabval Ltab38 Ftab38 F0tab38 Ltab14 Ftab14 F0tab14 Rdatad Rdatat Rbufs1 Rbufs2 Rtabval Rtab38 Rtab14 ND Z38 Z14 H2 H9 H18 H20 H21 H22 H25 K0 K1 K2 K3 K4 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (dith_wpl_facts2 w h HOK Hw1 Hh1) as (Gs & Gdw & Gw4 & Gw16 & Gds & Psh & Pdh & Psh1 & Pdh1).
  destruct HOK as (DV & Hw2 & Hh2 & Hsz).
  set (wplt := wpl_of w 8) in *. set (wpld := wpl_of w 2) in *.
  set (nd := (4 * (wpld * h))%Z) in *. set (ns := (4 * (wplt * h))%Z) in *. set (nb := (4 * wplt)%Z) in *.
  destruct (blk_range C A M md (Z_to_bv 64 datad) nd CK HW Ldatad ltac:(lia)) as [Gdatad TOPdatad]. rewrite u_Z2bv in Gdatad, TOPdatad by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ldatad) as (_ & ALdatad & _). rewrite u_Z2bv in ALdatad by lia. apply mod16_mod4 in ALdatad.
  destruct (blk_range C A M md (Z_to_bv 64 datat) ns CK HW Ldatat ltac:(lia)) as [Gdatat TOPdatat]. rewrite u_Z2bv in Gdatat, TOPdatat by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ldatat) as (_ & ALdatat & _). rewrite u_Z2bv in ALdatat by lia. apply mod16_mod4 in ALdatat.
  destruct (blk_range C A M md (Z_to_bv 64 bufs1) nb CK HW Lbufs1 ltac:(lia)) as [Gbufs1 TOPbufs1]. rewrite u_Z2bv in Gbufs1, TOPbufs1 by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lbufs1) as (_ & ALbufs1 & _). rewrite u_Z2bv in ALbufs1 by lia. apply mod16_mod4 in ALbufs1.
  destruct (blk_range C A M md (Z_to_bv 64 bufs2) nb CK HW Lbufs2 ltac:(lia)) as [Gbufs2 TOPbufs2]. rewrite u_Z2bv in Gbufs2, TOPbufs2 by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lbufs2) as (_ & ALbufs2 & _). rewrite u_Z2bv in ALbufs2 by lia. apply mod16_mod4 in ALbufs2.
  destruct (blk_range C A M md (Z_to_bv 64 tabval) 1024%Z CK HW Ltabval ltac:(lia)) as [Gtabval TOPtabval]. rewrite u_Z2bv in Gtabval, TOPtabval by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ltabval) as (_ & ALtabval & _). rewrite u_Z2bv in ALtabval by lia. apply mod16_mod4 in ALtabval.
  destruct (blk_range C A M md (Z_to_bv 64 tab38) 1024%Z CK HW Ltab38 ltac:(lia)) as [Gtab38 TOPtab38]. rewrite u_Z2bv in Gtab38, TOPtab38 by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ltab38) as (_ & ALtab38 & _). rewrite u_Z2bv in ALtab38 by lia. apply mod16_mod4 in ALtab38.
  destruct (blk_range C A M md (Z_to_bv 64 tab14) 1024%Z CK HW Ltab14 ltac:(lia)) as [Gtab14 TOPtab14]. rewrite u_Z2bv in Gtab14, TOPtab14 by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ltab14) as (_ & ALtab14 & _). rewrite u_Z2bv in ALtab14 by lia. apply mod16_mod4 in ALtab14.
  assert (GT : (4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\ 4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\
                4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0)%Z) by (repeat split; first [assumption | lia]).
  assert (GEO : low2_geom s datad w h wpld datat wplt bufs1 bufs2 tabval tab38 tab14).
  { unfold low2_geom. fold nd ns nb. repeat split; first [assumption | lia]. }
  assert (BR : blk_regs A [(datad, nd); (datat, ns); (bufs1, nb); (bufs2, nb); (tabval, 1024%Z); (tab38, 1024%Z); (tab14, 1024%Z)]).
  { unfold blk_regs. repeat (apply Forall_cons; [cbn [fst snd]; split; [assumption | split; lia]|]). apply Forall_nil. }
  assert (GDJ : low2_disj s datad h wpld datat wplt bufs1 bufs2 tabval tab38 tab14).
  { unfold low2_disj, LWL. fold nd ns nb. apply (pairwise_blocks C A M md ((s - 288)%Z, 288%Z) _ CK HW ltac:(cbn [fst]; lia) BR). exact ND. }
  assert (GDT : pairwise (RT tabval tab38 tab14)).
  { unfold RT. apply (pairwise_live C A M md _ CK HW).
    - unfold blk_regs. repeat (apply Forall_cons; [cbn [fst snd]; split; [assumption | split; lia]|]). apply Forall_nil.
    - cbn [map fst]. inversion ND as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst.
      inversion ND3 as [|x4 l4 N4 ND4]; subst. exact ND4. }
  assert (SOKt : forall t, List.In t [tabval; tab38; tab14] -> store_ok SEGS M (Z_to_bv 64 t) 1024 = true).
  { intros t [<- | [<- | [<- | []]]]; [exact (blk_sok C A M md tabval 1024 CK HW Ltabval ltac:(lia) ltac:(lia) ltac:(lia))
      | exact (blk_sok C A M md tab38 1024 CK HW Ltab38 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (blk_sok C A M md tab14 1024 CK HW Ltab14 ltac:(lia) ltac:(lia) ltac:(lia))]. }
  assert (ROT : regions_ok SEGS M (RT tabval tab38 tab14)).
  { intros r Hr. unfold RT in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd]; (repeat split; try lia); apply SOKt; cbn [List.In]; tauto. }
  assert (TV0 : forall t, (forall i, (0 <= i < 1024)%Z -> M (at_ (Z_to_bv 64 t) i) = Some (Z_to_bv 8 0)) -> (0 <= t)%Z -> (t + 1024 < 2 ^ 47)%Z -> tab_ok SEGS true tv_ok M t).
  { intros t Zt H0 H1. apply zero_tab_ok; [lia | lia | left; lia |]. intros i Hi. pose proof (Zt i Hi) as ZZ. unfold at_ in ZZ. rewrite u_Z2bv in ZZ by lia. exact ZZ. }
  destruct (T_run al_rom tabval tab38 tab14 GT GDT M regs ROT (TV0 tab38 Z38 ltac:(lia) ltac:(lia)) (TV0 tab14 Z14 ltac:(lia) ltac:(lia)) H20 H21 H22)
    as (r1 & M1 & RUN1 & RI1 & TK38 & TK14 & AG1).
  assert (RO0 : regions_ok SEGS M [((s - 288)%Z, 80%Z); ((s - 200)%Z, 16%Z); ((s - 176)%Z, 8%Z); RD datad h wpld; RB1 wplt bufs1; RB2 wplt bufs2; RS h datat wplt]).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [unfold RD, RB1, RB2, RS; cbn [fst snd]; fold nd ns nb; (repeat split; try lia);
      first [ (apply (W_sok_win C A M md _ _ CK HW); [lia | cbn; lia])
            | exact (blk_sok C A M md datad nd CK HW Ldatad ltac:(lia) ltac:(lia) ltac:(lia)) | exact (blk_sok C A M md bufs1 nb CK HW Lbufs1 ltac:(lia) ltac:(lia) ltac:(lia))
            | exact (blk_sok C A M md bufs2 nb CK HW Lbufs2 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (blk_sok C A M md datat ns CK HW Ldatat ltac:(lia) ltac:(lia) ltac:(lia)) ] |]). destruct Hr. }
  pose proof (regions_ok_grows SEGS M M1 _ RO0 (proj1 RI1)) as RO1.
  assert (KEEPC : forall z (n : nat) v, (c_top C - LSTK <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z -> rdn SEGS M (Z_to_bv 64 z) n = Some v -> rdn SEGS M1 (Z_to_bv 64 z) n = Some v).
  { intros z n v Hz Hn R. rewrite <- R. apply (rinv_rdn SEGS _ M M1 z n RI1); [lia | exact Hn |].
    intros r Hr. unfold RT in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd]; right; lia. }
  assert (TK1 : tabs_ok tabval tab38 tab14 M1).
  { unfold tabs_ok. split; [|split; [exact TK38 | exact TK14]].
    apply (tab_ok_sok SEGS false M M1 tabval wr_readable_img (proj1 RI1) (SOKt tabval ltac:(cbn [List.In]; tauto))); lia. }
  assert (KC1 : kcs s w h wpld datat wplt M1).
  { unfold kcs. repeat split;
      match goal with |- rdn _ _ (Z_to_bv 64 (s - ?k)) ?n = _ => replace (s - k)%Z with (s + - k)%Z by lia; apply KEEPC; [lia | cbn; lia | assumption] end. }
  destruct (L_run al_rom s datad w h wpld datat wplt bufs1 bufs2 tabval tab38 tab14 GEO GDJ M1 r1 RO1 TK1 KC1 ltac:(rewrite (AG1 2%bv) by notin_list; rewrite H2; f_equal; lia) ltac:(rewrite (AG1 9%bv) by notin_list; exact H9) ltac:(rewrite (AG1 18%bv) by notin_list; exact H18) ltac:(rewrite (AG1 20%bv) by notin_list; exact H20) ltac:(rewrite (AG1 21%bv) by notin_list; exact H21) ltac:(rewrite (AG1 22%bv) by notin_list; exact H22) ltac:(rewrite (AG1 25%bv) by notin_list; exact H25)) as (r2 & M2 & RUN2 & RI2 & KP2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact (msteps_trans _ _ _ _ RUN1 RUN2) |].
  set (RALL := RT tabval tab38 tab14 ++ RWL s datad h wpld wplt bufs1 bufs2).
  assert (RI : rinv RALL M M2).
  { apply (rinv_trans RALL M M1 M2); [apply (rinv_incl _ RALL M M1 RI1) | apply (rinv_incl _ RALL M1 M2 RI2)]; intros r Hr; unfold RALL; apply in_or_app; tauto. }
  destruct (rinv_WP C A Ar M md M2 s RALL CK HW SUB Hhi RI) as [HW' PM'].
  { intros r Hr. unfold RALL, RT, RWL, RD, RB1, RB2 in Hr. cbn [In app] in Hr. fold nd nb in Hr.
    repeat (destruct Hr as [<- | Hr]; [first
      [ (left; cbn [fst snd]; lia)
      | (right; exists (Z_to_bv 64 tabval), 1024%Z; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; first [assumption | lia])
      | (right; exists (Z_to_bv 64 tab38), 1024%Z; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; first [assumption | lia])
      | (right; exists (Z_to_bv 64 tab14), 1024%Z; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; first [assumption | lia])
      | (right; exists (Z_to_bv 64 datad), nd; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; first [assumption | lia])
      | (right; exists (Z_to_bv 64 bufs1), nb; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; first [assumption | lia])
      | (right; exists (Z_to_bv 64 bufs2), nb; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; first [assumption | lia]) ] |]). destruct Hr. }
  apply (HK r2 M2 HW' PM').
  - apply (regs_agree_kept regs r2 [2; 3; 4; 9; 18; 20; 21; 22; 25]%bv D2K_CLOB); [|vm_compute; reflexivity].
    intros r Hr. rewrite (KP2 r Hr). apply AG1. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [notin_list |]). destruct Hr.
  - intros a Ha. apply (proj2 RI). intros r Hr IR. unfold inreg in IR. unfold RALL, RT, RWL, RD, RB1, RB2 in Hr. cbn [In app] in Hr. fold nd nb in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in IR; lia |]). destruct Hr.
  - intros q k Lq NI i Hi. apply (proj2 RI).
    destruct (blk_range C A M md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
    assert (Ea : u (at_ q i) = (u q + i)%Z) by (unfold at_; rewrite u_Z2bv by lia; reflexivity).
    assert (APq : forall b n, live A (Z_to_bv 64 b) = Some n -> (0 <= b < 2 ^ 64)%Z -> (0 <= n)%Z -> List.In (Z_to_bv 64 b) [Z_to_bv 64 datad; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] -> (u q + k <= b \/ b + n <= u q)%Z).
    { intros b n Lb Rb Hn Ib. assert (NEq : q <> Z_to_bv 64 b) by (intros ->; exact (NI Ib)).
      pose proof (blk_apart_g C A M md _ _ k n CK HW Lq Lb NEq ltac:(lia) Hn) as AP. rewrite (u_Z2bv b) in AP by lia. exact AP. }
    pose proof (APq datad nd Ldatad Rdatad ltac:(lia) ltac:(cbn [List.In]; tauto)) as APdatad.
    pose proof (APq bufs1 nb Lbufs1 Rbufs1 ltac:(lia) ltac:(cbn [List.In]; tauto)) as APbufs1.
    pose proof (APq bufs2 nb Lbufs2 Rbufs2 ltac:(lia) ltac:(cbn [List.In]; tauto)) as APbufs2.
    pose proof (APq tabval 1024%Z Ltabval Rtabval ltac:(lia) ltac:(cbn [List.In]; tauto)) as APtabval.
    pose proof (APq tab38 1024%Z Ltab38 Rtab38 ltac:(lia) ltac:(cbn [List.In]; tauto)) as APtab38.
    pose proof (APq tab14 1024%Z Ltab14 Rtab14 ltac:(lia) ltac:(cbn [List.In]; tauto)) as APtab14.
    clear APq.
    intros r Hr IR. unfold inreg in IR. rewrite Ea in IR. unfold RALL, RT, RWL, RD, RB1, RB2 in Hr. cbn [In app] in Hr. fold nd nb in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in IR; lia |]). destruct Hr.
Qed.
End Dith2W.
