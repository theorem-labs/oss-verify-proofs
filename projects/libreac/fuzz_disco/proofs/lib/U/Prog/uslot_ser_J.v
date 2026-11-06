From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_ws slot_ser_J0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c snprintf_c json_scalar_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs uslot_ser uslot_ser_J0 uslot_ser_J2 uslot_ser_J6.
Import ListNotations.
Open Scope Z_scope.

Theorem uslot_ser_J : json_scalar_contract -> jtok_is_contract -> user_J_spec.
Proof.
  intros JS JT. unfold user_J_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X lo buf count B os j208 j232 jk jo jv Esp Es1 Es2 Es3 Es4 Es8 Es10 Es11 HX0 HX16 HX Hb Hbl FB JR Hcnt BB
    C176 C208 C216 C232 CK CO CJ JTB MI ST HK HI.
  unfold uSER_JSON, uSER_R12. unfold JSON_SCALAR_K, IMG_END in *.
  change (Z.of_nat (length B)) with (jlen B) in *.
  assert (FB' : Forall (fun c => 0 <= c < 256) B) by (revert FB; apply Forall_impl; intros x Hx; lia).
  pose proof (munch_refl [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 2376)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply (uslot_R10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m buf count B os);
      first [eassumption | lia]. }
  intros ms' [(a0x & a1x & s6x & Ec & Eos & E) | (a0x & a1x & i1 & Hi1 & JO & E)].
  - subst ms' count os.
    destruct (user_split m (X + 1056) (X + 1056) 0 1296 1296 jo ltac:(lia) ltac:(lia) CO) as [C0 _].
    apply evt_done. do 20 eexists. exists m, (repeat (Z_to_bv 8 0) 4), j208, j232, jk, jo, jv.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact C208|]. split; [exact C232|]. split; [exact CK|]. split; [exact C0|].
    split; [eapply urw_addr; [exact CO|lia]|]. split; [exact CJ|reflexivity].
  - subst ms'.
    destruct (user_split m (X + 232) (X + 240) 8 16 24 j232 ltac:(lia) ltac:(lia) C232) as [C232a C240r].
    destruct (user_split m (X + 240) (X + 248) 8 8 16 (skipn 8 j232) ltac:(lia) ltac:(lia) C240r) as [C240 C248].
    clear C232 C240r.
    destruct (user_split m (X + 1024) (X + 1044) 20 12 32 jk ltac:(lia) ltac:(lia) CK) as [CK1 CK2].
    destruct (user_split m (X + 1044) (X + 1048) 4 8 12 (skipn 20 jk) ltac:(lia) ltac:(lia) CK2) as [CV CW].
    clear CK CK2.
    destruct (user_split m (X + 2352) (X + 2372) 20 4 24 jv ltac:(lia) ltac:(lia) CJ) as [CJ1 CP]. clear CJ.
    destruct (user_split m (X + 1056) (X + 1056) 0 1296 1296 jo ltac:(lia) ltac:(lia) CO) as [CA0 _].
    pose proof CV as CVw. apply user_cb in CVw as (Lk & _ & _).
    pose proof CP as CPw. apply user_cb in CPw as (Lv & _ & _).
    pose proof CJ1 as CJw. apply user_cb in CJw as (Ljv & _ & _).
    eapply evt_cut.
    { eapply (uobj_loop JS JT (length B)) with (lo := lo) (X := X) (b := buf) (c := 0) (i := i1) (count := count)
        (B := B) (acc := []) (os := os) (jk := firstn 20 jk) (vpk := firstn 4 (skipn 20 jk)) (jv := firstn 20 jv)
        (vpad := skipn 20 jv) (jo := jo) (j208 := j208) (j232 := firstn 8 j232) (j240 := firstn 8 (skipn 8 j232))
        (j248 := skipn 8 (skipn 8 j232));
        first [eassumption | reflexivity | lia | (eapply urw_addr; [eassumption | lia])]. }
    intros ms' (ra3 & t03 & t13 & t23 & s03 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s53 & s63 & s73 &
                t33 & t43 & t53 & t63 & m3 & jk3 & jv3 & jo3 & j2083 & j2323 & j2403 & j2483 & E & MU3 & WM3 & MI3 &
                ST3 & C2083 & C2323 & C2403 & C2483 & CK3 & CV3 & CA3 & CR3 & CJ3 & CP3).
    subst ms'. transport_after_call rsegs m m3 MU3 WM3. clear MU3 WM3.
    apply evt_done. do 20 eexists.
    exists m3, (skipn 20 jv), j2083, (j2323 ++ j2403 ++ j2483),
      (jk3 ++ firstn 4 (skipn 20 jk) ++ skipn 4 (skipn 20 jk)), jo3, (jv3 ++ skipn 20 jv).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact C2083|].
    split.
    { change 24%nat with (8 + (8 + 8))%nat. apply ucb_join; [exact C2323|].
      apply ucb_join; [eapply urw_addr; [exact C2403|lia]|]. eapply urw_addr; [exact C2483|lia]. }
    split.
    { change 32%nat with (20 + (4 + 8))%nat. apply ucb_join; [exact CK3|].
      apply ucb_join; [eapply urw_addr; [exact CV3|lia]|]. eapply urw_addr; [exact CW|lia]. }
    split; [exact CA3|]. split; [exact CR3|].
    split; [|exact Lv]. change 24%nat with (20 + 4)%nat. apply ucb_join; [exact CJ3|]. eapply urw_addr; [exact CP3|lia].
Qed.
