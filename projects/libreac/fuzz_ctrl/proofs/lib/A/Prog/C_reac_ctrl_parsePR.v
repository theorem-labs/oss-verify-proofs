(* lib/A/Prog/C_reac_ctrl_parsePR.v -- fuzz_ctrl image A (asan, libreac v1.9.0): the frame release of the cgif-form
   glue pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v), after the re-based stretch reac_ctrl_parseF_rbody.v
   (Module RBodyFOn): its writes Wf2 S FS fra jj 1 ++ [(ob, ob + 36)] are the journal's awr bytes or the class-1 flag
   byte, and with the flag byte read 0 the journal steps to stack_free_state 1 pos (own drops (1, pos)).
     rcpPR_wr       the write cases: image B's rcpB_wq_cases and the J3 block of a Theorem Labs lane's
                    lib/B/Prog/C_reac_ctrl_parsePf.v (@ 3e03efa9e16 / 258208c7d59), on image A's write list Wf2.
     rcpPR_release  A.ProgWorldAstack.ctl_release_of_free_law at cid 1, with AR_laws_ok / astack_free_law_ok (core,
                    proved) and CtrlImg.ctrl_wx; its flag premise from the bytes_at premise (YP09.mbyte = mrd).
   B -> A: lib.B.ProgWorldAstack -> A.ProgWorldAstack; lib.B.ProgBridgeData.rsegs_wx_nowrap -> A.Prog.CtrlImg.ctrl_wx;
   PL.Wq o S Fr FL -> RBodyFOn.Wf2 S FS fra jj 1 ++ [(ob, ob + 36)]; lib.B.AsanRT.shadow_addr -> A.AsanRT.shadow_addr;
   Hypothesis LAWS / ASF -> YG0q.AR_laws_ok / YG0t.astack_free_law_ok.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT ProgWorld ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c CtrlImg reac_ctrl_parseF_rbody.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YA0n YM05 YI16 YG0f YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09 YG00 YG01 YG0n YG0q YG0t.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module PWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldAstack.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module CI := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.
Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_rbody.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RK04R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04R.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Module RG0t := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0t.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Local Notation rsegs := AI0.rsegs (only parsing).

Section PR.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.

(* The statements a Theorem Labs lane's assembly C_reac_ctrl_parseP.v cites (a Theorem Labs lane 15:38Z), as Definitions; rcpPR_wr / rcpPR_release below prove
   them verbatim. *)
Definition rcpPR_wr_stmt : Prop :=
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc S2 (W : RA0n.world rsegs) mem2 md2 k pos jj fra ob o S,
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
  sp0 - STK <= S - 8800 -> S <= sp0 ->
  fra = RG0f.frame_addr lyc 1 pos -> fra = SMC.fs_frame (RG0f.ly_F lyc) 1 jj ->
  SMC.fs_flag (RG0f.ly_F lyc) 1 jj = RG0f.flag_addr lyc 1 pos ->
  ((o = 0 /\ ob = fra + 32) \/ (o <> 0 /\ ob = o)) ->
  (o <> 0 -> forall a, o <= a < o + 36 ->
     RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc own a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ LF.outside (RB.RBodyFOn.Wf2 S (RG0f.ly_F lyc) fra jj 1 ++ [(ob, ob + 36)]) a ->
  RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc ((1, pos) :: own) a \/
  a = RG0f.flag_addr lyc 1 pos.

Definition rcpPR_release_stmt : Prop :=
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc S2 (W : RA0n.world rsegs)
    (ms ms' : machine_state) md2 md' k pos jj fra ob o S RNG,
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms) md2 k ->
  RK04R.fsteps rsegs RNG ms ms' -> RK04R.fp_avoids (RA0n.w_H W) RNG ->
  LF.munch (RB.RBodyFOn.Wf2 S (RG0f.ly_F lyc) fra jj 1 ++ [(ob, ob + 36)]) (ms_mem ms) (ms_mem ms') ->
  RK04.same_but_materialized md2 md' ->
  LM.bytes_at rsegs (ms_mem ms') (RG0f.flag_addr lyc 1 pos) [Z_to_bv 8 0] ->
  sp0 - STK <= S - 8800 -> S <= sp0 ->
  fra = RG0f.frame_addr lyc 1 pos -> fra = SMC.fs_frame (RG0f.ly_F lyc) 1 jj ->
  SMC.fs_flag (RG0f.ly_F lyc) 1 jj = RG0f.flag_addr lyc 1 pos ->
  ((o = 0 /\ ob = fra + 32) \/ (o <> 0 /\ ob = o)) ->
  (o <> 0 -> forall a, o <= a < o + 36 ->
     RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc own a) ->
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc (RG01.stack_free_state 1 pos S2) W (ms_mem ms') md' k.

(* A.AsanRT's shadow address (Wf2's) is the core's YG0f.shadow_addr (in_frames'). *)
Lemma rcpPR_sh_eq : forall x, ART.shadow_addr x = RG0f.shadow_addr x.
Proof. intros x. unfold ART.shadow_addr, ART.ASAN_K, RG0f.shadow_addr, RG0f.SHADOW_OFF. lia. Qed.

(* The write cases (image B: rcpB_wq_cases and the awr bullets of the J3 block): the window is the stack disjunct,
   the frame and its 16 shadow bytes are in_frames (1, pos), the flag byte is the right disjunct, the hint interval
   is empty, and the record bytes [ob, ob + 36) are frame bytes (o = 0) or the caller's awr bytes, own widened. *)
Lemma rcpPR_wr :
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc S2 (W : RA0n.world rsegs) mem2 md2 k pos jj fra ob o S,
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
  sp0 - STK <= S - 8800 -> S <= sp0 ->
  fra = RG0f.frame_addr lyc 1 pos -> fra = SMC.fs_frame (RG0f.ly_F lyc) 1 jj ->
  SMC.fs_flag (RG0f.ly_F lyc) 1 jj = RG0f.flag_addr lyc 1 pos ->
  ((o = 0 /\ ob = fra + 32) \/ (o <> 0 /\ ob = o)) ->
  (o <> 0 -> forall a, o <= a < o + 36 ->
     RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc own a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ LF.outside (RB.RBodyFOn.Wf2 S (RG0f.ly_F lyc) fra jj 1 ++ [(ob, ob + 36)]) a ->
  RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc ((1, pos) :: own) a \/
  a = RG0f.flag_addr lyc 1 pos.
Proof.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W mem2 md2 k pos jj fra ob o S
    _ Hlo Hhi Efr _ Efl Hob Hawr a _ Hout.
  assert (EB1 : RG00.fs_frame_bytes 1 = 128) by reflexivity.
  assert (FR : forall x, fra <= x < fra + 128 ->
                 RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc ((1, pos) :: own) x).
  { intros x Hx. unfold RCbq.awr_byte. right. right. right.
    exists 1, pos. split; [left; reflexivity|]. left.
    unfold RG0n.in_zr. cbn [fst snd]. rewrite EB1, <- Efr. lia. }
  unfold RB.RBodyFOn.Wf2 in Hout. cbn [app LF.outside] in Hout.
  assert (Cases : (S - 8800 <= a < S) \/ (fra <= a < fra + 128) \/
                  (ART.shadow_addr fra <= a < ART.shadow_addr fra + 16) \/
                  a = SMC.fs_flag (RG0f.ly_F lyc) 1 jj \/ (ob <= a < ob + 36)) by lia.
  destruct Cases as [Hw|[Hf|[Hsh|[Hl|Hb]]]].
  - left. unfold RCbq.awr_byte. left. lia.
  - left. exact (FR a Hf).
  - left. unfold RCbq.awr_byte. right. right. right.
    exists 1, pos. split; [left; reflexivity|]. right.
    unfold RG0n.in_zr. cbn [fst snd]. rewrite EB1, <- Efr, <- rcpPR_sh_eq.
    assert (E16 : 128 / 8 = 16) by reflexivity. rewrite E16. lia.
  - right. rewrite Hl. exact Efl.
  - destruct Hob as [(_ & Eob) | (Hne & Eob)].
    + left. apply FR. lia.
    + left. subst ob. destruct (Hawr Hne a Hb) as [Q|[Q|[Q|(cid & pos' & Hown & Q)]]].
      * left. exact Q.
      * right. left. exact Q.
      * right. right. left. exact Q.
      * right. right. right. exists cid, pos'. split; [right; exact Hown | exact Q].
Qed.

(* The release (image B: the J3 block of pb_reac_ctrl_parse): A.ProgWorldAstack.ctl_release_of_free_law at cid 1, its
   awr / flag premise by rcpPR_wr, its flag premise (YP09.mbyte) from the bytes_at premise. *)
Lemma rcpPR_release :
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc S2 (W : RA0n.world rsegs)
    (ms ms' : machine_state) md2 md' k pos jj fra ob o S RNG,
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms) md2 k ->
  RK04R.fsteps rsegs RNG ms ms' -> RK04R.fp_avoids (RA0n.w_H W) RNG ->
  LF.munch (RB.RBodyFOn.Wf2 S (RG0f.ly_F lyc) fra jj 1 ++ [(ob, ob + 36)]) (ms_mem ms) (ms_mem ms') ->
  RK04.same_but_materialized md2 md' ->
  LM.bytes_at rsegs (ms_mem ms') (RG0f.flag_addr lyc 1 pos) [Z_to_bv 8 0] ->
  sp0 - STK <= S - 8800 -> S <= sp0 ->
  fra = RG0f.frame_addr lyc 1 pos -> fra = SMC.fs_frame (RG0f.ly_F lyc) 1 jj ->
  SMC.fs_flag (RG0f.ly_F lyc) 1 jj = RG0f.flag_addr lyc 1 pos ->
  ((o = 0 /\ ob = fra + 32) \/ (o <> 0 /\ ob = o)) ->
  (o <> 0 -> forall a, o <= a < o + 36 ->
     RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc S2) lyc own a) ->
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc (RG01.stack_free_state 1 pos S2) W (ms_mem ms') md' k.
Proof.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W ms ms' md2 md' k pos jj fra ob o S RNG
    HJ Hrun Hfp Hm Hs Hfl Hlo Hhi Efr Efr' Efl Hob Hawr.
  apply (PWA.ctl_release_of_free_law B 1 (RG0q.AR_laws_ok rsegs B) (RG0t.astack_free_law_ok rsegs B) CI.ctrl_wx
           ltac:(lia) STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W ms ms' md2 md' k pos RNG
           (RB.RBodyFOn.Wf2 S (RG0f.ly_F lyc) fra jj 1 ++ [(ob, ob + 36)]) HJ Hrun Hfp Hm Hs).
  - exact (rcpPR_wr STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W (ms_mem ms) md2 k pos jj fra ob o S
             HJ Hlo Hhi Efr Efr' Efl Hob Hawr).
  - destruct Hfl as (_ & _ & F0).
    specialize (F0 O ltac:(cbn [length]; lia)). cbn [nth_error] in F0. change (Z.of_nat 0) with 0 in F0.
    rewrite Z.add_0_r in F0. unfold LM.mrd, LM.wa in F0. unfold RP09.mbyte. exact F0.
Qed.

End PR.
