(* check_latest_sent_seg_runs_entry: the entry run (0x848bc to the loop head 0x84974, or to the epilogue 0x84b4c when
   len = 0) and the epilogue run (0x84b4c to the return) of the ASan image-B walk of check_latest_sent. Shapes in
   check_latest_sent_seg_runs.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  AsanKA AsanKAProof TWorldB check_state_wake_c check_latest_sent_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  check_latest_sent_seg_model check_latest_sent_seg_runs.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The step tactics' hypothesis transport, extended with the facts this walk carries: cls_body, cls_wok,
   addressable and mem_grows (image A's block, 91f8c40cf11 lib/A/Prog/check_latest_sent_seg_runs.v). Local, so a
   file that Requires this one keeps the library's own transport. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU;
              [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | MG : mem_grows ?mq m |- _ => apply (clsr_grow_write mq m (wa a) bs) in MG
  | HK : cls_wok ?d m |- _ => apply (cls_wok_write d m (wa a) bs) in HK
  | HB : cls_body m ?p ?bsy |- _ =>
      first [ apply (clsr_body_write m p bsy a bs) in HB; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | fail 100 "store meets the body:" a ]
  | HA : addressable m ?p ?n |- _ =>
      first [ apply (cls_addr_store m p n a bs) in HA; [ | lia | simpl_sizes; slia | cls_app_tac ]
            | fail 100 "store not in application memory:" a ]
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* ---- the epilogue, 0x84b4c .. 0x84b84 ---- *)
Lemma cls_run_epi : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (spv : Z) (j : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 : word)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  0 <= spv -> spv + 160 <= 2 ^ 64 ->
  rw_cells rsegs m spv (cls_fr_e j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ExecF.rng RNG spv 160 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 (spv + 160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m (seg_rom rsegs)) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR y1 (Z_to_bv 64 spv) gp tp t0 t1 t2 y8 y9 a0 a1 a2 a3 a4 a5 a6 a7
              y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
        F (Z_to_bv 64 543564) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc spv j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
    gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 H0 H1 FR RG K.
  unfold cls_fr_e in FR.
  (* 0x84b4c .. 0x84b7c: ra, s0 .. s11 reloaded *)
  do 13 step.
  (* 0x84b80 addi sp,sp,160 *)
  step.
  try rewrite (unsigned_lit spv) by lia.
  (* 0x84b84 ret *)
  step.
  exact K.
Qed.

(* ---- the helpers of cls_run_entry ---- *)

(* The world over the entry's stores: they all fall in the frame or in dp, the frame lies off G_HARNESS_B's hull and
   dp off every range of G_HARNESS_B, so tw_at holds at every memory the run reaches, with the same Bw. *)
Lemma clsr_entry_kept : forall (m m' : word -> option byte) (spv dp : Z) (Bw : list byte),
  tw_at TMAP_B (csw_view m) Bw ->
  munch [(spv, spv + 160); (dp, dp + 4)] m m' ->
  (spv + 160 <= TransportGB.G_HARNESS_B_LO \/ TransportGB.G_HARNESS_B_HI <= spv) ->
  (forall b n, In (b, n) TransportGB.G_HARNESS_B -> dp + 4 <= b \/ b + n <= dp) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof.
  intros m m' spv dp Bw HW MU OG ODG.
  apply (tw_kept_GB (csw_view m) _ Bw HW).
  intros b n i Hin Hi.
  pose proof (TransportGB.G_HARNESS_B_in_hull (b, n) Hin) as Hh.
  cbn [fst snd] in Hh. unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in Hh, OG.
  assert (Hr : 0 <= b + i < 2 ^ 64) by lia.
  unfold csw_view, mrd. rewrite (MU (wa (b + i))); [reflexivity|].
  rewrite (wa_unsigned (b + i) Hr). cbn [outside].
  destruct (ODG b n Hin) as [D|D]; (split; [lia | split; [lia | exact I]]).
Qed.

(* `beqz` of an unsigned 64-bit value *)
Lemma clsr_entry_eqb0 : forall v, 0 <= v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* the UBSan alignment test of dp at 0x848f8: andi a1,a2,3 *)
Lemma clsr_entry_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. exact (Z.land_ones x 2 ltac:(lia)). Qed.

(* `snez a0,s2` at 0x84934 = `sltu a0,zero,s2`, with bp > 0 *)
Lemma clsr_entry_snez : forall d, 0 < d < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 d) = Z_to_bv 64 1.
Proof.
  intros d Hd. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  replace (0 <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* the two paths of the instrumented check of the store at dp meet at 0x84928: clsr_entry_join r pc J states the
   goal at pc for every value of register r (the one register the check's handler writes), clsr_entry_close r J
   closes a path that reached pc (image A's clsr_pre_join / clsr_pre_close) *)
Local Ltac clsr_entry_join r pc J :=
  lazymatch goal with |- ExecF.evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    assert (J : forall y : word, ExecF.evtF segs RNG Q (MS (tset p y R) F (Z_to_bv 64 pc) fc rv m ro))
  end.
Local Ltac clsr_entry_close r J := let w := reg_val r in exact (J w).

(* ---- the entry, 0x848bc .. 0x84970 ---- *)
Lemma cls_run_entry : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (lo sp0 bp len dp : Z) (Bw body : list byte) (v0 : word)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  cls_bounds (sp0 - 160) dp bp len -> cls_app (sp0 - 160) 160 -> cls_app dp 4 ->
  cls_off (sp0 - 160) dp bp len -> cls_rng RNG (sp0 - 160) dp ->
  Z.of_nat (length body) = len ->
  lo <= sp0 - 160 ->
  stk rsegs m lo sp0 ->
  asan_cells m ->
  cls_kw m ->
  cls_mem m Bw body dp bp len v0 ->
  (* the len = 0 exit, at 0x84b4c *)
  (forall (m' : word -> option byte) (j : list byte)
          (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
           x28 x29 x30 x31 : word),
     length j = 56%nat ->
     rw_cells rsegs m' (sp0 - 160) (cls_fr_e j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     cls_mem m' Bw body dp bp len (Z_to_bv 64 0) ->
     munch (cls_W (sp0 - 160) dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     len = 0 ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR x1 (Z_to_bv 64 (sp0 - 160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 543564) fc None m' (seg_rom rsegs))) ->
  (* the loop head, at 0x84974, with pos = 0 *)
  (forall (m' : word -> option byte) (j0 : list byte)
          (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word),
     length j0 = 8%nat ->
     rw_cells rsegs m' (sp0 - 160) (cls_fr j0 dp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     cls_mem m' Bw body dp bp len (Z_to_bv 64 0) ->
     munch (cls_W (sp0 - 160) dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     0 < len ->
     ExecF.evtF rsegs RNG Q
       (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 gp tp
              (sp0 - 160) dp bp len 0)
           F (Z_to_bv 64 543092) fc None m' (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 sp0) gp tp t0 t1 t2 s0 s1
              (Z_to_bv 64 bp) (Z_to_bv 64 len) (Z_to_bv 64 dp) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 542908) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc lo sp0 bp len dp Bw body v0
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HBD HAPs HAPd HOFF HRNG Hlen HLO ST CELLS KW HMEM KEXIT KHEAD.
  remember (sp0 - 160) as spv eqn:Espv.
  assert (Esp0 : sp0 = spv + 160) by lia. subst sp0. clear Espv.
  unfold cls_bounds in HBD. destruct HBD as (Hspv0 & Hspv1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  unfold cls_off in HOFF.
  destruct HOFF as (OG & OGOT & OCK & OKS & OKD & ODF & OBF & ODG & OBC & OBQ & OBN & OBD).
  unfold cls_rng in HRNG.
  destruct HRNG as (RFR & RGOT & RCK & RDP & RSD & RKS & RCMD & RSCMD & RQ & RSQ & RNQ).
  unfold cls_mem in HMEM. destruct HMEM as (HW & DPC & HBODY & ADC & ADQ & ADD & ADB & HWOK).
  destruct CELLS as (CK & GCK & _). unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  unfold cls_kw, CLS_KSENT, CLS_KVAL in KW. unfold CLS_KSENT in OKS, OKD, RKS.
  unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in OG.
  pose proof (munch_refl (cls_W spv dp) m) as MU. unfold cls_W in MU.
  pose proof (munch_refl [(spv, spv + 160); (dp, dp + 4)] m) as MU2.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (mem_grows_refl m) as MG.
  carve_frame 160%nat ST.
  rewrite Z.add_0_r in FR, ST.
  clear ST HLO.
  (* 0x848bc addi sp,sp,-160 *)
  step.
  replace (spv + 160 + -160) with spv by lia.
  (* 0x848c0 .. 0x848f0 the 13 saved registers *)
  do 13 step.
  (* 0x848f4 mv s1,a1 *)
  step.
  (* 0x848f8 andi a1,a2,3; 0x848fc bnez a1,0x84b88: dp mod 4 = 0 (cls_bounds), not taken *)
  step.
  step.
  rewrite (unsigned_lit dp) by lia. rewrite clsr_entry_land3, Hdp4, bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x84900 mv s0,a2; 0x84904 mv s2,a0; 0x84908 / 0x8490c a0 = [GOT_CELL_K] = CELL_K; 0x84910 s7 = [CELL_K] *)
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDG : ov_read_bytes rsegs mm (wa 670960) 8 = Some (le8 (wa 706168)));
    [ replace (wa 670960) with (wa (670960 + 0)) by reflexivity;
      rewrite (bytes_at_read rsegs mm 670960 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia);
      reflexivity | ];
    assert (RDC : ov_read_bytes rsegs mm (wa 706168) 8 = Some (le8 (wa 2147450880)));
    [ replace (wa 706168) with (wa (706168 + 0)) by reflexivity;
      rewrite (bytes_at_read rsegs mm 706168 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia);
      reflexivity | ]
  end.
  do 5 step.
  clear RDG RDC CK GCK.
  (* 0x84914 srli a0,a2,3; 0x84918 add a0,a0,s7: a0 = the shadow address of dp *)
  step. rewrite (unsigned_lit dp) by lia. rewrite cls_shr3.
  step.
  (* 0x8491c sd a0,48(sp) *)
  step.
  (* 0x84920 lb a0,0(a0): the shadow byte of dp *)
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (cls_sh_load mm dp 4 0 4 ADD ltac:(lia) ltac:(lia) ltac:(lia)) as (k & MK & SK);
    rewrite Z.add_0_r in MK, SK; change (4 - 1) with 3 in SK; unfold ASAN_K in MK;
    pose proof (rd1 mm _ _ MK) as RDK
  end.
  step.
  clear MK RDK.
  (* ---- 0x84928, where the check's two paths meet: a1 is dp & 3 = 0 or (dp & 7) + 3 ---- *)
  clsr_entry_join 11 543016 JOIN.
  2: { (* 0x84924 bnez a0,0x84b98 *)
       step. rewrite sxb_eq0.
       destruct SK as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_entry_close 11 JOIN.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)). cbn [negb]. cbv iota.
         (* 0x84b98 andi a1,s0,7; 0x84b9c addi a1,a1,3; 0x84ba0 blt a1,a0,0x84928: the handler goes back *)
         step. step. step.
         rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit dp) by lia.
         rewrite (cls_lts_lit (dp mod 8 + 3) k ltac:(lia)).
         rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
         clsr_entry_close 11 JOIN. }
  intros x11. cbv beta iota delta [tset].
  destruct (Z.eq_dec len 0) as [L0|L0].
  - (* len = 0: the empty body holds at every memory, so it is not carried over the store at dp *)
    lazymatch type of HBODY with cls_body ?mm _ _ =>
      assert (HBN : forall m' : word -> option byte, cls_body m' bp body)
        by (intros m'; exact (clsr_body_nil mm m' bp body HBODY ltac:(lia)))
    end.
    clear HBODY.
    (* 0x84928 sw zero,0(s0) *)
    step.
    (* 0x8492c beqz s1,0x84b4c: taken, the epilogue *)
    step.
    rewrite (clsr_entry_eqb0 len) by lia. rewrite (proj2 (Z.eqb_eq len 0) L0). cbv iota.
    lazymatch goal with FR : rw_cells _ ?mm spv (?c1 :: ?c2 :: ?rest) |- _ =>
      pose proof (clsr_entry_kept m mm spv dp Bw HW MU2 OG ODG) as HW';
      pose proof (rw_cells_merge rsegs mm spv [] [c1; c2] rest FR) as FRE;
      pose proof FR as FRW; destruct FRW as [[FRwf _] _]
    end.
    cbn [app cells_size csize Nat.add] in FRE.
    cbn [cells_wf cell_wf] in FRwf.
    lazymatch type of FRE with rw_cells _ ?mm _ (CB _ ?j :: _) =>
      apply (KEXIT mm j)
    end.
    + cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8. cbn [length]. lia.
    + exact FRE.
    + unfold cls_mem.
      split; [exact HW'|]. split; [exact DPC|]. split; [exact (HBN _)|].
      split; [exact ADC|]. split; [exact ADQ|]. split; [exact ADD|]. split; [exact ADB | exact HWOK].
    + exact MU.
    + exact WMo.
    + exact MG.
    + exact L0.
  - (* len <> 0: the body is off dp *)
    specialize (OBD ltac:(lia)).
    (* 0x84928 sw zero,0(s0) *)
    step.
    (* 0x8492c beqz s1,0x84b4c: not taken *)
    step.
    rewrite (clsr_entry_eqb0 len) by lia. rewrite (proj2 (Z.eqb_neq len 0) L0). cbv iota.
    (* 0x84930 li s9,0; 0x84934 snez a0,s2 *)
    step. step. rewrite (clsr_entry_snez bp) by lia.
    (* 0x84938 sd a0,40(sp) *)
    step.
    (* 0x8493c auipc a0; 0x84940 auipc a1; 0x84944 auipc s11 = 0x5df944; 0x84948 andi a2,s0,7 *)
    do 4 step.
    rewrite ?cls_wrap64_7. rewrite (unsigned_lit dp) by lia. rewrite land7.
    (* 0x8494c addi a0 = g_cmd; 0x84950 sd a0,32(sp) *)
    step. step.
    (* 0x84954 ld a0 = the constant-pool word at 0x10338, kept off the frame and dp by cls_off *)
    lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RKW : ov_read_bytes rsegs mm (wa 66360) 8 = Some (le8 (wa 14757395258967641293)));
      [ replace (wa 66360) with (wa (66360 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 66360 _ 0 8 KW ltac:(lia)) by (rewrite length_le8; lia);
        reflexivity | ]
    end.
    step.
    clear RKW.
    (* 0x84958 sd a0,24(sp) *)
    step.
    (* 0x8495c addi a2,a2,3; 0x84960 sd a2,8(sp) *)
    step. step.
    (* 0x84964 auipc a0; 0x84968 addi a0 = g_q; 0x8496c sd a0,16(sp); 0x84970 li s10,1023 *)
    do 4 step.
    lazymatch goal with FR : rw_cells _ ?mm spv (CB _ ?j0 :: _) |- _ =>
      pose proof (clsr_entry_kept m mm spv dp Bw HW MU2 OG ODG) as HW';
      pose proof FR as FRW; destruct FRW as [[FRwf _] _];
      apply (KHEAD mm j0)
    end.
    + cbn [cells_wf cell_wf] in FRwf. exact (proj1 FRwf).
    + exact FR.
    + unfold cls_mem.
      split; [exact HW'|]. split; [exact DPC|]. split; [exact HBODY|].
      split; [exact ADC|]. split; [exact ADQ|]. split; [exact ADD|]. split; [exact ADB | exact HWOK].
    + exact MU.
    + exact WMo.
    + exact MG.
    + lia.
Qed.
