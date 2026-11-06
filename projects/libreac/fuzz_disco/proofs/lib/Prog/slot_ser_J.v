From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_defs memset_c memset.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c jtok_is_c snprintf_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_J0 slot_ser slot_ser_J2 slot_ser_J6.
Import ListNotations.
Open Scope Z_scope.

Theorem ser_J : json_scalar_contract -> jtok_is_contract -> ser_J_spec.
Proof.
  intros JS JT. unfold ser_J_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X lo buf now count B os j192 j216 j224 jk jo jv Esp Es0 Es2 Es8 Es3 Es4 Es11 HX0 HX16 HX Hnow Hb Hbl FB JR Hcnt BB
    C192 C200 C216 C224 CK CO CJ JTB MI ST HK HI.
  unfold SER_JSON, SER_R12. unfold JSON_SCALAR_K, IMG_END in *.
  change (Z.of_nat (length B)) with (jlen B) in *.
  assert (FB' : Forall (fun c => 0 <= c < 256) B).
  { revert FB. apply Forall_impl. intros x Hx. lia. }
  assert (HJL : JSON_SCALAR_L = 0x1fe28) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (unfold pf_bytes; rewrite length_map, length_app; unfold jlen; cbn [length]; lia).
  pose proof (munch_refl [(lo, X); (X + 192, X + 200); (X + 216, X + 232); (X + 992, X + 2344)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply (slot_R10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m buf count B os);
      first [eassumption | lia]. }
  intros ms' [(a0x & a1x & a2x & a3x & s10x & Ec & Eos & E) | (a0x & a1x & a2x & a3x & i1 & Hi1 & JO & E)].
  - subst ms' count os.
    destruct (ser_split m (X + 1024) (X + 1024) 0 1296 1296 jo ltac:(lia) ltac:(lia) CO) as [C0 _].
    apply evt_done. do 21 eexists. exists m, (repeat (Z_to_bv 8 0) 4), j192, j216, j224, jk, jo, jv.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact C192|]. split; [exact C216|]. split; [exact C224|]. split; [exact CK|].
    split; [exact C0|]. split; [eapply rw_addr; [exact CO|lia]|]. split; [exact CJ|reflexivity].
  - subst ms'.
    destruct (ser_split m (X + 992) (X + 1012) 20 12 32 jk ltac:(lia) ltac:(lia) CK) as [CK1 CK2].
    destruct (ser_split m (X + 1012) (X + 1016) 4 8 12 (skipn 20 jk) ltac:(lia) ltac:(lia) CK2) as [CV CW].
    clear CK CK2.
    destruct (ser_split m (X + 2320) (X + 2340) 20 4 24 jv ltac:(lia) ltac:(lia) CJ) as [CJ1 CP]. clear CJ.
    destruct (ser_split m (X + 1024) (X + 1168) 144 1152 1296 jo ltac:(lia) ltac:(lia) CO) as [CO1 CR]. clear CO.
    pose proof CV as CVw. apply ser_cb in CVw as (Lk & _ & _).
    pose proof CP as CPw. apply ser_cb in CPw as (Lv & _ & _).
    pose proof CJ1 as CJw. apply ser_cb in CJw as (Ljv & _ & _).
    subst sp s0 s2 s3 s4 s8 s11.
    step. step. step. step. step.
    eapply evt_cut.
    { eapply memset_holds; [|exact MI]. rewrite !unsigned_lit by lia. exact CO1. }
    intros ms' (t0x & t1x & t2x & a1y & a2y & a3y & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m1 &
                E & MU1 & WM1 & MI1 & CZ).
    subst ms'. rewrite !unsigned_lit in MU1, CZ by lia.
    transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
    rewrite (ret_pc_even 0x13940) by (first [lia | reflexivity]).
    assert (CZ1 : rw_cells rsegs m1 (X + 1024) [CB 144 (repeat (Z_to_bv 8 0) 144)]) by exact CZ. clear CZ.
    destruct (ser_split m1 (X + 1024) (X + 1024) 0 144 144 _ ltac:(lia) ltac:(lia) CZ1) as [CA0 _].
    step. step. rewrite neg_lit. step. step. step.
    eapply evt_cut.
    { eapply (obj_loop JS JT (length B)) with (lo := lo) (X := X) (b := buf) (c := 0) (i := i1) (count := count)
        (now := now) (B := B) (acc := []) (os := os) (jk := firstn 20 jk) (vpk := firstn 4 (skipn 20 jk))
        (jv := firstn 20 jv) (vpad := skipn 20 jv) (j216 := j216) (j192 := j192) (jr := skipn 144 jo);
        first [eassumption | reflexivity | (f_equal; lia) | lia | (eapply rw_addr; [eassumption | lia])]. }
    intros ms' (ra3 & t03 & t13 & t23 & s13 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s53 & s93 & s103 &
                t33 & t43 & t53 & t63 & m3 & jk3 & jv3 & j2163 & j1923 & jo3 & E & MU3 & WM3 & MI3 & ST3 & CA3 & CR3 &
                CK3 & CJ3 & C2163 & C1923).
    subst ms'. lazymatch type of MU3 with munch _ ?mq _ => transport_after_call rsegs mq m3 MU3 WM3 end.
    clear MU3 WM3.
    apply evt_done. do 21 eexists.
    exists m3, (skipn 20 jv), j1923, j2163, (le8 (Z_to_bv 64 (buf + 1))),
      (jk3 ++ firstn 4 (skipn 20 jk) ++ skipn 4 (skipn 20 jk)), jo3, (jv3 ++ skipn 20 jv).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact C1923|]. split; [exact C2163|]. split; [apply ser_c8; exact C224|].
    split.
    { change 32%nat with (20 + (4 + 8))%nat. apply cb_join; [exact CK3|].
      apply cb_join; [eapply rw_addr; [exact CV|lia]|]. eapply rw_addr; [exact CW|lia]. }
    split; [exact CA3|]. split; [exact CR3|].
    split; [|exact Lv]. change 24%nat with (20 + 4)%nat. apply cb_join; [exact CJ3|]. eapply rw_addr; [exact CP|lia].
Qed.
