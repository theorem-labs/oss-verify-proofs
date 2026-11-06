(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnArith.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac WU_num_bits_word.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr DivModel DivLoopPure DivTop.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require DivLA.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_expand W_ctx BnLeaves BnUAlign BnUJoin BnCall DivLA W_lshift W_rshift W_ctx_end W_ctx_get W_copy BnAssoc W_div_tail W_div_pad.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].




(* [comment removed for export] *)
Lemma la_run : forall r (ls : lstate bptr),
  bn_left_align (tree_ops bptr) r ls =
  TRet (64 - num_bits_word (nth (bn_top (getbn r ls) - 1) (bn_buf (getbn r ls)) 0),
        setbn r (bn_with_buf (getbn r ls) (splice (bn_buf (getbn r ls)) 0
                   (fst (lshift_limbs (firstn (bn_top (getbn r ls)) (bn_buf (getbn r ls))) (64 - num_bits_word (nth (bn_top (getbn r ls) - 1) (bn_buf (getbn r ls)) 0)) 0)))) ls).
Proof. reflexivity. Qed.

Lemma bbind_get_set : forall {B} r (g : bignum bptr -> bignum bptr) (f : unit -> BM (M := btree bptr) B) (ls : lstate bptr),
  bbind (tree_ops bptr) (bbind (tree_ops bptr) (bget (tree_ops bptr) r) (fun b => bset (tree_ops bptr) r (g b))) f ls =
  f tt (setbn r (g (getbn r ls)) ls).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_cell L c k :=
  lazymatch L with
  | c :: ?post => k (@nil cell) post
  | ?x :: ?rest => split_cell rest c ltac:(fun pre post => k (x :: pre) post)
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_DIV_FIXED_TOP : Z := 0x1193f4.
Definition BN_DIV_STACK : Z := 256 + 16384.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition nonpool (r : bnref) : Prop := forall i, r <> RPool i.

  Lemma bn_div_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (dv rm num dvs : bnref) (adv arm anum advs : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_DIV_STACK -> tp = wz RATP ->
    ref_at ls OW AD dv adv -> ref_at ls OW AD rm arm -> ref_at ls OW AD num anum -> ref_at ls OW AD dvs advs ->
    a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz (ad_ctx AD) ->
    nonpool dv -> nonpool rm -> nonpool num -> nonpool dvs -> dv <> num -> dv <> dvs ->
    (1 <= bn_top (getbn dvs ls))%nat -> nth (bn_top (getbn dvs ls) - 1) (bn_buf (getbn dvs ls)) 0 <> 0 ->
    implM usegs (interp (embed (bn_div_fixed_top (tree_ops bptr) dv rm num dvs ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV_FIXED_TOP) fc None m (seg_rom usegs)).
  Proof.
    intros until advs. intros PRE -> HAdv HArm HAnum HAdvs -> -> -> -> -> NPdv NPrm NPnum NPdvs NEdn NEdd HTOPD HTOPNZ.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_DIV_STACK, BN_DIV_FIXED_TOP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold bn_div_fixed_top.
    pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    unfold implM. iprefix.
    carve_frame 256%nat ST. do 15 step. do 3 step. step. do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (FBlo : lo <= bv_unsigned sp + -256) by lia.
    assert (FBsp : bv_unsigned sp + -256 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m fr s ls m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m CEIL GLO' FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m CEIL GLO' FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) CEIL FBlo FBsp SPR2 A) as BPC.
    clear HEAP LS AUX ST ERR MI MU WM HWL WOK FR PRE.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_CTX_START_STACK ENV LS1 ltac:(unfold BN_CTX_START_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_CTX_start_leaves ls)|].
      eapply (BN_CTX_start_walk HM) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA); [exact PRE1 | reflexivity | reflexivity]. }
    cbv beta. intros [u1 ls2] st2 ms2 [PO LEAF2]. apply BPC in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & -> & CP2 & _).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP2) as (ENV2 & LS2).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP2) as RS2.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152076)) with (Z_to_bv 64 1152076) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear ENV LS1 PRE1 CP2 m1.
    pose proof (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m CEIL GLO' FBlo FBsp SPB) as CSIL.
    assert (HWLs : forall OWx, Forall (w_lib OWx lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (intros OWx; constructor; [left; cbn; lia| constructor]).
    assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx AD EA []) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (intros OWx lsx; constructor; [apply w_stack; cbn; lia| constructor]).
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
    assert (HAdv2 : ref_at ls2 OW2 AD dv adv) by (destruct ENV2 as (_ & _ & _ & _ & _ & _ & _ & _ & RS & _); apply RS; exact HAdv).
    destruct (ref_at_inb _ _ _ _ _ ADB2 HAdv2) as (qd & Ad & nd & _ & Hind & Rd1 & Rd2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV2) Hind) as (DA0 & _ & _ & DAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KD; zify_cond KD. 2:{ exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
    clear KD qd Ad nd Hind Rd1 Rd2 DA0 DAC.
    do 2 zstep.
    (* [comment removed for export] *)
    destruct SOK2 as (_ & _ & _ & _ & _ & _ & CK2).
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENV2 LS2 ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv2 & PRE2).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_CTX_get_leaves ls2); exact (proj1 (proj2 (proj2 CK2)))|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv2) (OW := OW2) (LB := LB) (AD := AD) (EA := EA); [exact PRE2 | reflexivity | reflexivity]. }
    cbv beta. intros [tmp ls3] st3 ms3 [PO LEAF3]. apply BPC in PO.
    destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & OW3 & -> & CP3 & ((atmp & HAtmp & ->) & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV2 CP3) as (ENV3 & LS3).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP3) as RS3.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152100)) with (Z_to_bv 64 1152100) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear ENV2 LS2 PRE2 CP3 m2 CK2 IDS2 ADB2 ERRB2.
    (* [comment removed for export] *)
    unfold MallocRep.wz. unfold implM. iprefix.
    do 3 zstep.
    pose proof ENV3 as ENV3'. pose proof LS3 as LS3'.
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS3') as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & CK4)).
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENV3' LS3' ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv4 & PRE4).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_CTX_get_leaves ls3); exact (proj1 (proj2 (proj2 CK4)))|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv4) (OW := OW3) (LB := LB) (AD := AD) (EA := EA); [exact PRE4 | reflexivity | reflexivity]. }
    cbv beta. intros [snum ls4] st4 ms4 [PO LEAF4]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & CP4 & ((asnum & HAsnum & ->) & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV3' CP4) as (ENV4 & LS4).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP4) as RS4.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152112)) with (Z_to_bv 64 1152112) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE4 CP4 CK4.
    (* [comment removed for export] *)
    env_open ENV4. unfold MallocRep.wz. unfold implM. iprefix.
    step. step. do 2 zstep.
    env_close CSIL HWLs WOKs ENV4 LS4 ENV4' LS4'.
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS4') as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & CK5)).
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENV4' LS4' ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv5 & PRE5).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_CTX_get_leaves ls4); exact (proj1 (proj2 (proj2 CK5)))|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv5) (OW := OW4) (LB := LB) (AD := AD) (EA := EA); [exact PRE5 | reflexivity | reflexivity]. }
    cbv beta. intros [sdiv ls5] st5 ms5 [PO LEAF5]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & CP5 & ((asdiv & HAsdiv & ->) & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV4' CP5) as (ENV5 & LS5).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP5) as RS5.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152128)) with (Z_to_bv 64 1152128) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE5 CP5 CK5.
    (* [comment removed for export] *)
    destruct LEAF2 as (L2a & L2b & _ & _). destruct LEAF3 as (L3a & L3b & _ & L3d). destruct LEAF4 as (L4a & L4b & _ & L4d). destruct LEAF5 as (L5a & L5b & _ & L5d).
    cbn [fst snd] in *.
    set (p0 := cx_pused (ls_ctx ls2)) in *.
    rewrite L3b in L4a. rewrite L4b, L3b in L5a.
    assert (NPget : forall r, nonpool r -> getbn r ls5 = getbn r ls).
    { intros r NP. rewrite L5d by (rewrite L4b, L3b; apply NP). rewrite L4d by (rewrite L3b; apply NP). rewrite L3d by apply NP. apply L2a. }
    assert (Etmp5 : getbn tmp ls5 = getbn tmp ls3).
    { rewrite L5d by (rewrite L4b, L3b, L3a; intros E; injection E; lia). rewrite L4d by (rewrite L3b, L3a; intros E; injection E; lia). reflexivity. }
    pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HAdv)))) as HAdv5. pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HArm)))) as HArm5.
    pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HAnum)))) as HAnum5. pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HAdvs)))) as HAdvs5.
    pose proof (RS5 _ _ (RS4 _ _ HAtmp)) as HAtmp5. pose proof (RS5 _ _ HAsnum) as HAsnum5.
    assert (NEts : tmp <> snum) by (rewrite L3a, L4a; intros E; injection E; lia).
    assert (NEtd : tmp <> sdiv) by (rewrite L3a, L5a; intros E; injection E; lia).
    assert (NEsd : snum <> sdiv) by (rewrite L4a, L5a; intros E; injection E; lia).
    assert (NPt : forall r, nonpool r -> r <> tmp) by (intros r NP; rewrite L3a; apply NP).
    assert (NPs : forall r, nonpool r -> r <> snum) by (intros r NP; rewrite L4a; apply NP).
    assert (NPd : forall r, nonpool r -> r <> sdiv) by (intros r NP; rewrite L5a; apply NP).
    clear L2a L2b L3a L3b L3d L4a L4b L4d L5a L5b L5d p0 RS2 RS3 RS4 RS5 HAdv2 HAtmp HAsnum ENV3 LS3 ENV3' LS3' ENV4 LS4 ENV4' LS4'.
    clear HAdv HArm HAnum HAdvs.
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS5) as (IDS5 & ADB5 & ERRB5 & SOK5).
    destruct (ref_at_inb _ _ _ _ _ ADB5 HAsdiv) as (qd & Ad & nd & _ & Hind & Rd1 & Rd2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV5) Hind) as (DA0 & _ & _ & DAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
    clear KD qd Ad nd Hind Rd1 Rd2 DA0 DAC.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAsdiv) as HVsd5. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAdvs5) as HVdvs5.
    pose proof (st_okm_getbn sdiv ls5 SOK5 HVsd5) as (_ & OKsd2 & _). pose proof (st_okm_getbn dvs ls5 SOK5 HVdvs5) as (OKdv1 & OKdv2 & OKdv3 & _).
    destruct (CPRE _ _ _ _ _ BN_COPY_STACK ENV5 LS5 ltac:(unfold BN_COPY_STACK, BN_EXPAND2_STACK; lia)) as (errv6 & PRE6).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_copy_leaves sdiv dvs ls5 (fun E => NPd dvs NPdvs (eq_sym E)) HVsd5 OKsd2 OKdv2)|].
      eapply (BN_copy_walk HM HF) with (lo := lo) (B := B) (errv := errv6) (OW := OW5) (LB := LB) (AD := AD) (EA := EA) (rx := sdiv) (ry := dvs) (ax := asdiv) (ay := advs);
        [exact PRE6 | reflexivity | exact HAsdiv | exact HAdvs5 | reflexivity | reflexivity]. }
    cbv beta. intros [u6 ls6] st6 ms6 [PO LEAF6]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & CP6 & (-> & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV5 CP6) as (ENV6 & LS6).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP6) as RS6.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152144)) with (Z_to_bv 64 1152144) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE6 CP6.
    (* [comment removed for export] *)
    destruct LEAF6 as (C6a & C6b & C6c & C6d & C6e & _). cbn [snd] in *.
    pose proof (RS6 _ _ HAdv5) as HAdv6. pose proof (RS6 _ _ HArm5) as HArm6. pose proof (RS6 _ _ HAnum5) as HAnum6. pose proof (RS6 _ _ HAdvs5) as HAdvs6.
    pose proof (RS6 _ _ HAtmp5) as HAtmp6. pose proof (RS6 _ _ HAsnum5) as HAsnum6. pose proof (RS6 _ _ HAsdiv) as HAsdiv6.
    assert (NPget6 : forall r, nonpool r -> getbn r ls6 = getbn r ls) by (intros r NP; rewrite C6a by (apply not_eq_sym, NPd, NP); apply NPget; exact NP).
    rewrite (NPget dvs NPdvs) in C6b, C6c, C6d, C6e, OKdv1, OKdv2, OKdv3.
    set (bd := getbn dvs ls) in *. set (dn := bn_top bd) in *.
    clear RS6 HAdv5 HArm5 HAnum5 HAdvs5 HAtmp5 HAsnum5 HAsdiv ENV5 LS5 IDS5 ADB5 ERRB5 SOK5 HVsd5 HVdvs5 OKsd2 NPget.
    pose proof (RH_nodup_l _ _ _ _ (proj1 ENV6)) as ND6.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS6) as (IDS6 & ADB6 & ERRB6 & SOK6).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HAsdiv6) as HVsd6.
    destruct (lib_state_open [] ls6 m6 OW6 AD EA sdiv asdiv LS6 ND6 HAsdiv6 ltac:(intros [])) as ((Dsd & BNsd & ARRsd) & (OKs1 & OKs2 & OKs3 & OKs4) & LSH6).
    set (b6 := getbn sdiv ls6) in *.
    destruct (bn_arr_facts st6 OW6 LB m6 (proj1 ENV6) ls6 AD EA IDS6 ADB6 sdiv Dsd HVsd6 ARRsd) as (Usd & LENsd & Dsd0 & DsdC & DsdI & DSEPsd).
    fold b6 in Usd, LENsd, DsdC, DsdI, DSEPsd.
    pose proof (DSEPsd sdiv asdiv HAsdiv6) as SEPsd. clear DSEPsd.
    destruct (ref_at_inb _ _ _ _ _ ADB6 HAsdiv6) as (qsd & Asd & nsd & _ & Hinsd & Rsd1 & Rsd2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV6) Hinsd) as (SDA0 & _ & _ & SDAC & SDAI).
    assert (HDsd : exists psd, bn_d b6 = Some psd /\ In (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)) OW6).
    { unfold bn_arr in ARRsd. destruct (bn_d b6) as [psd|]; [exists psd; split; [reflexivity| exact (proj1 ARRsd)]|].
      exfalso. destruct ARRsd as [_ E]. unfold bn_dmax in C6e. rewrite E in C6e. cbn in C6e. lia. }
    destruct HDsd as (psd & Edsd & Hinpsd).
    unfold bn_cells in BNsd. rewrite C6b, C6c in BNsd. unfold BN_WORDS_MAX in OKs3, OKdv3.
    env_open ENV6.
    match goal with MUx : munch _ m6 m6 |- _ => clear MUx end. match goal with WMx : wmono _ m6 m6 |- _ => clear WMx end.
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6) as MU6.
    pose proof (wmono_refl usegs m6) as WM6.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
    clear KD.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ (proj1 ENV6) ADB6 HAsdiv6) as (SDP & SD8).
    pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENV6) Hinpsd) as (DSP & DS8).
    zstep. rewrite (land7 asdiv) by exact SD8.
    chk ltac:(fun C => clear - C; lia).
    zstep.
    step. rewrite (sx32_small (Z.of_nat dn)) by lia.
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by lia.
    zstep. rewrite lts_signed by lia. if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    step. do 2 zstep.
    replace (Dsd + (Z.of_nat dn + -1) ≪ 3) with (Dsd + 8 * (Z.of_nat dn - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 2 zstep. rewrite ?land64_small by (unfold bn_dmax in *; lia).
    replace (0 <? Dsd) with true by (symmetry; apply Z.ltb_lt; exact DSP).
    replace (Dsd + 8 * (Z.of_nat dn - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DSP HTOPD; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    do 4 zstep.
    rewrite (lxor_signbit63' (Z.of_nat dn + -1)) by (clear - HTOPD OKs3 C6e OKs2; unfold bn_dmax in *; lia).
    replace (Z.of_nat dn + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - HTOPD; lia).
    replace (Dsd + 8 * (Z.of_nat dn - 1) <? Dsd) with false by (symmetry; apply Z.ltb_ge; clear - HTOPD; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    zstep. rewrite (land7 (Dsd + 8 * (Z.of_nat dn - 1))) by (clear - DS8; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    (* [comment removed for export] *)
    set (dtop := nth (dn - 1) (bn_buf bd) 0) in *.
    assert (Edtop : nth (dn - 1) (bn_buf b6) 0 = dtop).
    { unfold dtop. rewrite <- (firstn_skipn dn (bn_buf b6)), <- (firstn_skipn dn (bn_buf bd)), C6d.
      rewrite !app_nth1 by (rewrite length_firstn; unfold bn_dmax in *; lia). reflexivity. }
    assert (Rdtop : 0 < dtop < 18446744073709551616).
    { assert (L : limb dtop) by (apply limbs_nth; exact OKdv1). unfold limb in L. rewrite BW_lit in L. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => 
      destruct (proj1 (limbarr_limbs_at usegs mx Dsd (bn_buf b6)) Usd) as (LAsd & WRsd) end.
    assert (Ntop : nth_error (bn_buf b6) (dn - 1) = Some dtop) by (rewrite <- Edtop; apply nth_error_nth'; unfold bn_dmax in *; lia).
    let ad := cur_mem_addr in
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => 
        pose proof (limbs_at_read_nth usegs mx Dsd (bn_buf b6) (dn - 1) dtop ad LAsd Ntop ltac:(unfold wa; f_equal; lia)) as RD end.
    zstep. clear RD.
    zstep.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
    assert (Edt : bv_unsigned (Z_to_bv 64 dtop) = dtop) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { match goal with STx : stk _ m6 _ _, MIx : mem_inv _ m6 |- _ =>
        eapply BN_num_bits_word_uspec with (lo := lo) (m := m6); [rewrite ESP; exact STx | rewrite ESP; lia | exact MIx] end. }
    intros ms' PO. unfold nbw_upost in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ESP, Edt in *.
    replace (ret_pc (Z_to_bv 64 1152236)) with (Z_to_bv 64 1152236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LAsd8 : limbs_at usegs m8 Dsd (bn_buf b6)).
    { eapply limbs_at_transport; [exact LAsd | exact MUc |]. cbn [disjoint_from]. fold (bn_dmax b6). split; [|exact I]. lia. }
    clear LAsd WRsd.
    match goal with STx : stk _ m6 _ _ |- _ => clear STx end.
    transport_after_call usegs m6 m8 MUc WMc.
    clear MUc WMc. match goal with MIx : mem_inv _ m6 |- _ => clear MIx end.
    (* [comment removed for export] *)
    set (nb := num_bits_word dtop) in *.
    assert (NB : 1 <= nb <= 64).
    { destruct (num_bits_word_spec dtop ltac:(lia)) as (B1 & _). pose proof (num_bits_word_le dtop 64 ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia)). fold nb in B1, H. lia. }
    set (af := firstn dn (bn_buf b6)).
    assert (Laf : length af = dn) by (unfold af; apply firstn_length_le; unfold bn_dmax in *; lia).
    assert (LAaf : limbs_at usegs m8 Dsd af).
    { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. exact (proj1 LAsd8). }
    assert (LArest : limbs_at usegs m8 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
    { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. destruct LAsd8 as [_ X]. fold af in X. rewrite Laf in X. exact X. }
    destruct (proj1 (limbarr_limbs_at usegs m8 Dsd (bn_buf b6)) Usd) as (_ & WRsd8).
    replace (Z_to_bv 64 (Z.of_nat dn)) with (Z_to_bv 64 (Z.of_nat (length af))) by (rewrite Laf; reflexivity).
    lazymatch type of FRe with rw_cells _ _ _ ?fr =>
    eapply la_ublock with (m := m8) (D := Dsd) (SP := bv_unsigned sp) (lo := lo) (a := af) (lb := 64 - nb) (FS := 256) (FB := bv_unsigned sp + -256) (FCELLS := fr) (nb := nb)
    end.
    { reflexivity. }
    { lia. }
    { lia. }
    { rewrite Laf. left. unfold bn_dmax in *. lia. }
    { exact NB. }
    { reflexivity. }
    { rewrite Laf. lia. }
    { unfold af. apply limbs_firstn. exact OKs1. }
    { exact LAaf. }
    { rewrite Laf. apply (wr_at_sub usegs m8 Dsd (8 * Z.of_nat (length (bn_buf b6))) 0 (8 * Z.of_nat dn)) in WRsd8; [rewrite Z.add_0_r in WRsd8; exact WRsd8 | lia | lia | unfold bn_dmax in *; lia]. }
    { exact FRe. }
    { exact STc. }
    { exact MIc. }
    intros m9 w5 w6 w10 w11 w13 w14 w15 w16 w17 w18 HRES FR9 ST9 MI9 MU9 WM9. rewrite Laf in MU9.
    set (sh := 64 - nb) in *.
    set (resl := fst (lshift_limbs af sh 0)) in *.
    assert (Lres : length resl = dn) by (unfold resl; rewrite lshift_limbs_len; exact Laf).
    assert (DJ9 : forall A k, (A + k <= Dsd \/ Dsd + 8 * Z.of_nat (bn_dmax b6) <= A) -> A + k <= bv_unsigned sp - 256 ->
              disjoint_from [(Dsd, Dsd + 8 * Z.of_nat dn); (bv_unsigned sp - 256, bv_unsigned sp)] A k).
    { intros A k H1 H2. cbn [disjoint_from]. unfold bn_dmax in *. lia. }
    eapply (rw_cells_transport usegs _ m8 m9) in BNsd; [| exact MU9 | exact WM9 | apply DJ9; cbn; lia].
    eapply (rw_cells_transport usegs _ m8 m9) in ERRe; [| exact MU9 | exact WM9 | apply DJ9; cbn; lia].
    assert (LArest9 : limbs_at usegs m9 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
    { eapply limbs_at_transport; [exact LArest | exact MU9 |]. cbn [disjoint_from]. rewrite length_skipn. unfold bn_dmax in *. lia. }
    set (nbuf := splice (bn_buf b6) 0 resl).
    assert (Lnbuf : length nbuf = bn_dmax b6) by (unfold nbuf, bn_dmax in *; rewrite splice_length by lia; reflexivity).
    assert (U9 : u64arr usegs m9 Dsd (wlimbs nbuf)).
    { apply limbarr_limbs_at. split.
      - unfold nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). change (0 + length resl)%nat with (length resl).
        change ([] ++ resl ++ skipn (length resl) (bn_buf b6)) with (resl ++ skipn (length resl) (bn_buf b6)).
        apply limbs_at_app. split; [exact HRES|]. rewrite Lres. exact LArest9.
      - rewrite Lnbuf. eapply wr_at_transport; [exact WRsd8 | exact WM9]. }
    assert (MU6' : munch [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6 m9).
    { eapply munch_trans; [exact MU6|]. eapply munch_weaken; [|exact MU9]. unfold sub_fp. intros xx Hxx. cbn [outside] in *. unfold bn_dmax in *. lia. }
    assert (WM6' : wmono usegs m6 m9) by (eapply wmono_trans; eauto).
    assert (LENnb : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
    clear MU6 WM6 MU9 WM9 Usd LENsd LAsd8 LAaf LArest LArest9 HRES WRsd8 DJ9 FRe STc MIc.
    (* [comment removed for export] *)
    step. step. zstep. step. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops]. rewrite la_run. cbn [tbind fst snd]. rewrite bbind_get_set.
    fold b6. rewrite C6b. fold dn. rewrite Edtop. fold nb. fold sh. fold af. fold resl. fold nbuf.
    rewrite (getbn_setbn_same_m sdiv _ ls6 HVsd6), setbn_setbn_same.
    set (sd3 := bn_with_neg (bn_with_buf b6 nbuf) false).
    unfold bbind at 1. cbn [bind tree_ops].
    assert (HWL6 : Forall (w_lib OW6 lo (bv_unsigned sp)) [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (qsd, Asd, nsd); cbn; auto|].
      constructor; [right; exists (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)); cbn; split; [exact Hinpsd| lia]| constructor]. }
    assert (WOK6 : Forall (w_ok OW6 LB ls6 AD EA [sdiv]) [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
    { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW6 LB ls6 AD EA false [sdiv] _ sdiv asdiv); [left; reflexivity| exact HAsdiv6| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OW6 LB ls6 AD EA false [sdiv] _ sdiv psd Dsd); [left; reflexivity| exact HVsd6| exact Edsd| exact Hinpsd| cbn [fst snd]; fold b6; lia| cbn [fst snd]; fold b6; lia]| constructor]. }
    pose proof (left_align_value af ltac:(unfold af; apply limbs_firstn; exact OKs1) ltac:(rewrite Laf; lia)) as LAV.
    rewrite Laf in LAV.
    assert (Eaft : nth (dn - 1) af 0 = dtop) by (unfold af; rewrite nth_firstn; destruct (Nat.ltb_spec (dn - 1) dn); [exact Edtop | lia]).
    rewrite Eaft in LAV. specialize (LAV ltac:(lia)). cbv zeta in LAV. fold nb in LAV. fold sh in LAV. fold resl in LAV.
    destruct LAV as (SH & LRES & _ & VRES & D0N).
    assert (LS7 : lib_state (setbn sdiv sd3 ls6) m10 OW6 AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls6 m10 OW6 AD EA sdiv asdiv); [| exact ND6| exact HAsdiv6| | |].
      - match goal with HEAPx : RHEAP st6 _ m6 |- _ => exact (lib_state_frame st6 LB [sdiv] ls6 m6 m10 OW6 AD EA _ HEAPx LSH6 MU6' WM6' WOK6) end.
      - exists Dsd. split.
        + unfold bn_cells, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite Lnbuf, C6b. fold dn. exact BNsd.
        + unfold bn_arr, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Edsd, Lnbuf. split; [exact Hinpsd| exact U9].
      - unfold bn_okm, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_buf bn_top bn_flags]. rewrite Lnbuf. unfold BN_WORDS_MAX.
        split; [unfold nbuf; apply splice_limbs; [exact OKs1| exact LRES]|]. split; [exact OKs2|]. split; [lia| exact OKs4].
      - apply ids_ok_setbn_same; [exact IDS6| exact HVsd6|]. unfold bn_blocks, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Lnbuf. reflexivity. }
    lazymatch type of ENV6 with cenv ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j _ _ _ _ _ =>
      lazymatch goal with FRx : rw_cells _ m10 (bv_unsigned sp + -256) ?fr' |- _ =>
        assert (ENV7 : cenv a b c d e f g h i j fr' st6 (setbn sdiv sd3 ls6) m10 OW6) end end.
    { apply cenv_setbn.
      match goal with FRx : rw_cells _ m10 (bv_unsigned sp + -256) ?fr', STx : stk _ m10 _ _, MIx : mem_inv _ m10, ERRx : rw_cells _ m10 3353076 _ |- _ =>
        eapply (CSIL _ fr'); [exact ENV6 | exact MU6' | exact WM6' | exact HWL6 | exact STx | unfold LX_ERRNO, RATP; exact ERRx | exact MIx | exact FRx | cbn; lia] end. }
    set (ls7 := setbn sdiv sd3 ls6) in *.
    assert (HAsnum7 : ref_at ls7 OW6 AD snum asnum) by (apply ref_at_setbn; exact HAsnum6).
    assert (HAnum7 : ref_at ls7 OW6 AD num anum) by (apply ref_at_setbn; exact HAnum6).
    destruct (lib_state_h_parts _ _ _ _ _ _ LS7) as (_ & _ & _ & SOK7).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAsnum7) as HVsn7. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAnum7) as HVnum7.
    pose proof (st_okm_getbn snum ls7 SOK7 HVsn7) as (_ & OKsn2 & _). pose proof (st_okm_getbn num ls7 SOK7 HVnum7) as (OKn1 & OKn2 & OKn3 & _).
    destruct (CPRE _ _ _ _ _ BN_LSHIFT_STACK ENV7 LS7 ltac:(unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv7 & PRE7).
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_lshift_leaves snum num sh ls7 (fun E => NPs num NPnum (eq_sym E)) SH HVsn7 OKsn2 OKn2)|].
      eapply (bn_lshift_fixed_top_walk HM HF) with (lo := lo) (B := B) (errv := errv7) (OW := OW6) (LB := LB) (AD := AD) (EA := EA) (rr := snum) (rx := num) (ar := asnum) (ax := anum) (n := sh);
        [exact PRE7 | reflexivity | exact HAsnum7 | exact HAnum7 | reflexivity | reflexivity | reflexivity | exact SH]. }
    cbv beta. intros [u8 ls8] st8 ms8 [PO LEAF8]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW8 & -> & CP8 & ->).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV7 CP8) as (ENV8 & LS8).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP8) as RS8.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152376)) with (Z_to_bv 64 1152376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE7 CP8.
    (* [comment removed for export] *)
    destruct LEAF8 as (L8a & L8b & L8c & L8d & L8e & _). cbn [snd] in *.
    assert (Enum7 : getbn num ls7 = getbn num ls) by (unfold ls7; rewrite getbn_setbn_other by (apply not_eq_sym, NPd, NPnum); apply NPget6; exact NPnum).
    rewrite Enum7 in L8b, L8c, L8d, L8e, OKn1, OKn2, OKn3.
    set (bnum := getbn num ls) in *. set (tn := bn_top bnum) in *.
    assert (Esd8 : getbn sdiv ls8 = sd3) by (rewrite L8a by exact NEsd; unfold ls7; apply getbn_setbn_same_m; exact HVsd6).
    assert (NPget8 : forall r, nonpool r -> getbn r ls8 = getbn r ls).
    { intros r NP. rewrite L8a by (apply not_eq_sym, NPs, NP). unfold ls7. rewrite getbn_setbn_other by (apply not_eq_sym, NPd, NP). apply NPget6. exact NP. }
    assert (Etmp8 : getbn tmp ls8 = getbn tmp ls6) by (rewrite L8a by (apply not_eq_sym; exact NEts); unfold ls7; apply getbn_setbn_other; apply not_eq_sym; exact NEtd).
    pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAdv6)) as HAdv8. pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HArm6)) as HArm8.
    pose proof (RS8 _ _ HAnum7) as HAnum8. pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAdvs6)) as HAdvs8.
    pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAtmp6)) as HAtmp8. pose proof (RS8 _ _ HAsnum7) as HAsnum8.
    pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAsdiv6)) as HAsdiv8.
    clear RS8 HAdv6 HArm6 HAnum6 HAdvs6 HAtmp6 HAsnum6 HAsdiv6 HAsnum7 HAnum7 ENV6 LS6 ENV7 LS7 LSH6 HWL6 WOK6 MU6' WM6' U9 BNsd SOK7 HVsn7 HVnum7 OKsn2 NPget6
          IDS6 ADB6 ERRB6 SOK6 ND6 Hinsd Hinpsd SEPsd DsdI DsdC Dsd0 SDA0 SDAC SDAI Rsd1 Rsd2 ARRsd LENnb Enum7.
    (* [comment removed for export] *)
    pose proof (RH_nodup_l _ _ _ _ (proj1 ENV8)) as ND8.
    destruct (lib_state_open [] ls8 m11 OW8 AD EA sdiv asdiv LS8 ND8 HAsdiv8 ltac:(intros [])) as ((Dsd8 & BNsd8 & _) & _ & _).
    destruct (lib_state_open [] ls8 m11 OW8 AD EA snum asnum LS8 ND8 HAsnum8 ltac:(intros [])) as ((Dsn8 & BNsn8 & _) & (OKsn1 & OKsn2 & OKsn3 & OKsn4) & _).
    rewrite Esd8 in BNsd8. unfold bn_cells in BNsd8, BNsn8. unfold sd3 in BNsd8. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsd8.
    rewrite C6b in BNsd8. rewrite L8b in BNsn8. unfold BN_WORDS_MAX in OKsn3, OKn3.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS8) as (_ & ADB8 & _ & _).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ (proj1 ENV8) ADB8 HAsnum8) as (SNP & SN8).
    assert (SNR : asnum + 24 <= alloc_ceiling).
    { destruct (ref_at_inb _ _ _ _ _ ADB8 HAsnum8) as (qq & Aq & nq & _ & Hinq & Rq1 & Rq2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV8) Hinq) as (_ & _ & _ & QC & _). clear - Rq2 QC. lia. }
    assert (SDR : 0 < asdiv /\ asdiv + 24 <= alloc_ceiling).
    { destruct (ref_at_inb _ _ _ _ _ ADB8 HAsdiv8) as (qq & Aq & nq & _ & Hinq & Rq1 & Rq2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV8) Hinq) as (Q0 & _ & _ & QC & _). clear - Rq1 Rq2 QC Q0. lia. }
    env_open ENV8.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
    clear KZ.
    step. step.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - SNP SNR CEIL LO SPR; lia); clear - C SNP; lia).
    step. zstep. rewrite (land7 asnum) by exact SN8.
    chk ltac:(fun C => clear - C; lia).
    step. step. rewrite (zx32_small (Z.of_nat dn)) by (unfold bn_dmax in *; lia).
    step.
    step. rewrite (sx32_small (Z.of_nat (tn + 1))) by (unfold bn_dmax in *; lia).
    step. do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat dn + 0)) by (unfold bn_dmax in *; lia). rewrite Z.add_0_r.
    step.
    env_close CSIL HWLs WOKs ENV8 LS8 ENV8' LS8'.
    (* [comment removed for export] *)
    ihere. to_implM. rewrite !bbind_get. rewrite Esd8. change (bn_top sd3) with (bn_top b6). rewrite C6b, L8b.
    lazymatch type of ENV8' with cenv _ _ _ _ _ _ _ _ _ _ ?FR8 _ _ _ _ =>
    lazymatch goal with |- implM _ (interp (embed (bbind _ _ ?REST0 _))) _ ?Q _ =>
      assert (CONT : forall stP lsP mP OWP (nP : nat) x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x28 x29 x30 x31,
                 cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m FR8 stP lsP mP OWP -> lib_state lsP mP OWP AD EA ->
                 ref_at lsP OWP AD dv adv -> ref_at lsP OWP AD rm arm -> ref_at lsP OWP AD num anum -> ref_at lsP OWP AD dvs advs ->
                 ref_at lsP OWP AD tmp atmp -> ref_at lsP OWP AD snum asnum -> ref_at lsP OWP AD sdiv asdiv ->
                 getbn sdiv lsP = sd3 -> (forall r, nonpool r -> getbn r lsP = getbn r ls) ->
                 bn_top (getbn snum lsP) = nP -> (dn + 1 <= nP)%nat -> (tn + 1 <= nP)%nat -> (nP <= dn + 1 \/ nP = tn + 1)%nat -> bn_neg (getbn snum lsP) = bn_neg bnum ->
                 firstn nP (bn_buf (getbn snum lsP)) = lsh_res bnum sh ++ repeat 0%Z (nP - (tn + 1)) ->
                 implM usegs (interp (embed (REST0 tt lsP))) stP Q
                   (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17
                            x18 (Z_to_bv 64 adv) (Z_to_bv 64 atmp) (Z_to_bv 64 asdiv) (Z_to_bv 64 anum) x23 x24 x25 (Z_to_bv 64 (Z.of_nat nP)) (Z_to_bv 64 advs) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x119638) fc None mP (seg_rom usegs)))
    end end.
    { intros stP lsP mP OWP nP q1 q5 q6 q7 q9 q11 q12 q13 q14 q15 q16 q17 q18 q23 q24 q25 q28 q29 q30 q31
             ENVP LSP HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP GSP NPgP TNP NP1 NP2 NP3 NEGP FNP.
      clear ENV8 LS8 ENV8' LS8' HAdv8 HArm8 HAnum8 HAdvs8 HAtmp8 HAsnum8 HAsdiv8 ND8 BNsd8 BNsn8 Dsd8 Dsn8 OKsn1 OKsn2 OKsn3 OKsn4 L8a L8b L8c L8d L8e Esd8 NPget8 Etmp8
            ADB8 SNP SN8 SNR SDR.
      cbv beta. rewrite bbind_get, TNP.
      (* [comment removed for export] *)
      pose proof (RH_nodup_l _ _ _ _ (proj1 ENVP)) as NDP.
      destruct (lib_state_h_parts _ _ _ _ _ _ LSP) as (IDSP & ADBP & ERRBP & SOKP).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsdivP) as HVsdP. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsnumP) as HVsnP.
      destruct (lib_state_open [] lsP mP OWP AD EA sdiv asdiv LSP NDP HAsdivP ltac:(intros [])) as ((DsdP & BNsdP & ARRsdP) & _ & _).
      destruct (lib_state_open [] lsP mP OWP AD EA snum asnum LSP NDP HAsnumP ltac:(intros [])) as ((DsnP & BNsnP & ARRsnP) & (OKp1 & OKp2 & OKp3 & OKp4) & _).
      destruct (bn_arr_facts stP OWP LB mP (proj1 ENVP) lsP AD EA IDSP ADBP sdiv DsdP HVsdP ARRsdP) as (UsdP & _ & DsdP0 & DsdPC & _ & _).
      rewrite GSP in BNsdP, UsdP, DsdPC. unfold bn_cells in BNsdP, BNsnP.
      unfold sd3 in BNsdP, UsdP, DsdPC. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsdP, UsdP, DsdPC.
      rewrite C6b in BNsdP. rewrite TNP in BNsnP. unfold BN_WORDS_MAX in OKp3.
      unfold bn_dmax in DsdPC. cbn [bn_buf] in DsdPC. rewrite Lnbuf in DsdPC.
      assert (LENnbP : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
      set (d0 := nth (dn - 1) nbuf 0).
      set (d1 := if (dn =? 1)%nat then 0 else nth (dn - 2) nbuf 0).
      assert (Lnb2 : (dn <= length nbuf)%nat) by (rewrite Lnbuf; unfold bn_dmax in *; lia).
      assert (LIMnb : limbs nbuf) by (unfold nbuf; apply splice_limbs; [exact OKs1 | exact LRES]).
      assert (Rd0 : 9223372036854775808 <= d0 < 18446744073709551616).
      { assert (L : limb d0) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. split; [|lia].
        unfold d0, nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). cbn [app]. rewrite app_nth1 by lia.
        change (2 ^ 63) with 9223372036854775808 in D0N. exact D0N. }
      assert (Rd1 : 0 <= d1 < 18446744073709551616).
      { unfold d1. destruct (dn =? 1)%nat; [lia|]. assert (L : limb (nth (dn - 2) nbuf 0)) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. lia. }
      destruct (ref_at_inb _ _ _ _ _ ADBP HAsdivP) as (qsP & AsP & nsP & _ & HinsP & RsP1 & RsP2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVP) HinsP) as (SP0 & _ & _ & SPC & SPI).
      destruct (ref_at_inb _ _ _ _ _ ADBP HAsnumP) as (qnP & AnP & nnP & _ & HinnP & RnP1 & RnP2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVP) HinnP) as (NP0 & _ & _ & NPC & NPI).
      (* [comment removed for export] *)
      assert (HSN : exists psn, bn_d (getbn snum lsP) = Some psn /\ In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWP).
      { unfold bn_arr in ARRsnP. destruct (bn_d (getbn snum lsP)) as [psn|]; [exists psn; split; [reflexivity| exact (proj1 ARRsnP)]|].
        exfalso. destruct ARRsnP as [_ E]. unfold bn_dmax in OKp2. rewrite E in OKp2. cbn in OKp2. lia. }
      destruct HSN as (psn & Edsn & HinsnP).
      assert (HSD : exists psd', In (psd', DsdP, 8 * Z.of_nat (bn_dmax sd3)) OWP).
      { rewrite GSP in ARRsdP. unfold bn_arr in ARRsdP. destruct (bn_d sd3) as [pp|]; [exists pp; exact (proj1 ARRsdP)|].
        exfalso. destruct ARRsdP as [_ E]. unfold sd3 in E. cbn [bn_with_neg bn_with_buf bn_buf] in E. rewrite E in Lnb2. cbn in Lnb2. lia. }
      destruct HSD as (psd' & HinsdP).
      pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVP) HinsnP) as (SNDP & SND8).
      pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVP) HinsdP) as (SDDP & SDD8).
      destruct (bn_arr_facts stP OWP LB mP (proj1 ENVP) lsP AD EA IDSP ADBP snum DsnP HVsnP ARRsnP) as (_ & _ & _ & DsnPC & _ & _).
      set (loop := (nP - dn)%nat) in *.
      assert (RLOOP : 0 < Z.of_nat loop < 8388609) by (unfold loop, bn_dmax in *; lia).
      assert (RNP : 0 < Z.of_nat nP < 8388609) by (unfold bn_dmax in *; lia).
      assert (RDN : 0 < Z.of_nat dn < 8388609) by (unfold bn_dmax in *; lia).
      assert (RSNP : DsnP + 8 * Z.of_nat nP <= alloc_ceiling) by (unfold bn_dmax in *; lia).
      assert (RSDP : DsdP + 8 * Z.of_nat dn <= alloc_ceiling) by (unfold bn_dmax in *; lia).
      env_open ENVP.
      unfold MallocRep.wz in *. unfold implM. iprefix.
      repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
      do 2 zstep.
      rewrite (bk_swrap32_small (Z.of_nat nP - Z.of_nat dn)) by (clear - RNP RDN; lia).
      replace (Z.of_nat nP + - Z.of_nat dn) with (Z.of_nat loop) by (unfold loop; clear - NP1; lia).
      replace (Z.of_nat nP - Z.of_nat dn) with (Z.of_nat loop) by (unfold loop; clear - NP1; lia).
      step.
      chk ltac:(fun C => clear - C; lia).
      step. step. step. do 2 zstep.
      replace (Z.of_nat loop ≪ 3) with (8 * Z.of_nat loop) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      do 2 zstep. rewrite ?land64_small by (clear - SNDP RSNP RLOOP NP1 CEIL LO SPR; unfold loop in *; lia).
      replace (0 <? DsnP) with true by (symmetry; apply Z.ltb_lt; exact SNDP).
      replace (DsnP + 8 * Z.of_nat loop <? 1) with false by (symmetry; apply Z.ltb_ge; clear - SNDP; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      zstep. step. do 3 zstep.
      rewrite (lxor_signbit63' (Z.of_nat loop)) by (clear - RLOOP; lia).
      replace (Z.of_nat loop + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear; lia).
      replace (DsnP + 8 * Z.of_nat loop <? 8 * Z.of_nat loop) with false by (symmetry; apply Z.ltb_ge; clear - SNDP; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      zstep. rewrite (bk_swrap32_small (Z.of_nat nP + -1)) by (clear - RNP; lia).
      zstep. rewrite lts_signed by (clear - RNP; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
      do 2 zstep.
      replace (DsnP + (Z.of_nat nP + -1) ≪ 3) with (DsnP + 8 * (Z.of_nat nP - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
      step.
      zstep. rewrite ?land64_small by (clear - SNDP RSNP RNP CEIL LO SPR; lia).
      replace (DsnP + 8 * (Z.of_nat nP - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - SNDP RNP; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      step. do 4 zstep.
      rewrite (lxor_signbit63' (Z.of_nat nP + -1)) by (clear - RNP; lia).
      replace (Z.of_nat nP + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - RNP; lia).
      replace (DsnP + 8 * (Z.of_nat nP - 1) <? DsnP) with false by (symmetry; apply Z.ltb_ge; clear - RNP; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      step.
      zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by (clear - RDN; lia).
      zstep. rewrite lts_signed by (clear - RDN; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
      step. step. do 2 zstep.
      replace (DsdP + (Z.of_nat dn + -1) ≪ 3) with (DsdP + 8 * (Z.of_nat dn - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      do 2 zstep. rewrite ?land64_small by (clear - SDDP RSDP RDN CEIL LO SPR; lia).
      replace (0 <? DsdP) with true by (symmetry; apply Z.ltb_lt; exact SDDP).
      replace (DsdP + 8 * (Z.of_nat dn - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - SDDP RDN; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' (Z.of_nat dn + -1)) by (clear - RDN; lia).
      replace (Z.of_nat dn + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - RDN; lia).
      replace (DsdP + 8 * (Z.of_nat dn - 1) <? DsdP) with false by (symmetry; apply Z.ltb_ge; clear - RDN; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - SDDP RSDP CEIL LO SPR; lia); clear - C SDDP; lia).
      zstep. rewrite (land7 (DsdP + 8 * (Z.of_nat dn - 1))) by (clear - SDD8; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      assert (N0 : nth_error nbuf (dn - 1) = Some d0) by (unfold d0; apply nth_error_nth'; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mR end.
      destruct (proj1 (limbarr_limbs_at usegs mR DsdP nbuf) UsdP) as (LAnbR & _).
      let ad := cur_mem_addr in
        pose proof (limbs_at_read_nth usegs mR DsdP nbuf (dn - 1) d0 ad LAnbR N0 ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD.
      zstep. step.
      eassert (C6D8 : _); [ |
        zstep; if_cases K1; zify_cond K1;
        [ (* [comment removed for export] *)
          assert (N1 : nth_error nbuf (dn - 2) = Some d1)
            by (unfold d1; replace (dn =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia); apply nth_error_nth'; lia);
          assert (DN2 : 2 <= Z.of_nat dn) by (rewrite ?unsigned_lit in K1 by (clear - RDN; lia); clear - K1 RDN; lia);
          zstep; rewrite (bk_swrap32_small (Z.of_nat dn + -2)) by (clear - RDN DN2; lia);
          zstep; rewrite lts_signed by (clear - RDN DN2; lia); if_cases KO; zify_cond KO; [exfalso; clear - KO; lia | clear KO];
          do 2 zstep;
          replace (DsdP + (Z.of_nat dn + -2) ≪ 3) with (DsdP + 8 * (Z.of_nat dn - 2)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
          chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - SDDP RSDP DN2 CEIL LO SPR; lia); clear - C SDDP DN2; lia);
          do 4 zstep;
          rewrite (lxor_signbit63' (Z.of_nat dn + -2)) by (clear - RDN DN2; lia);
          replace (Z.of_nat dn + -2 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - DN2; lia);
          replace (DsdP + 8 * (Z.of_nat dn - 2) <? DsdP) with false by (symmetry; apply Z.ltb_ge; clear - DN2; lia);
          cbn [Z.b2z Z.lxor];
          chk ltac:(fun C => clear - C; lia);
          zstep; rewrite (land7 (DsdP + 8 * (Z.of_nat dn - 2))) by (clear - SDD8; Z.div_mod_to_equations; lia);
          chk ltac:(fun C => clear - C; lia);
          (let ad := cur_mem_addr in
           pose proof (limbs_at_read_nth usegs mR DsdP nbuf (dn - 2) d1 ad LAnbR N1 ltac:(unfold wa; f_equal; lia)) as RD);
          zstep; clear RD; forget_temps; exact C6D8
        | do 2 zstep;
          setreg_at 18%Z (Z_to_bv 64 d1) ltac:(unfold d1; replace (dn =? 1)%nat with true by (symmetry; apply Nat.eqb_eq; rewrite ?unsigned_lit in K1 by (clear - RDN; lia); clear - K1; lia); reflexivity);
          forget_temps; exact C6D8 ] ].
      intros j5 j6 j7 j10 j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31.
      (* [comment removed for export] *)
      zstep. step. zstep.
      (* [comment removed for export] *)
      repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
      env_close CSIL HWLs WOKs ENVP LSP ENVQ LSQ.
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAdvP) as HVdvP.
      pose proof (st_okm_getbn dv lsP SOKP HVdvP) as (_ & OKdvP2 & _).
      destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENVQ LSQ ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errvQ & PREQ).
      ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply implM_embed_leaves; [apply (bn_wexpand_leaves2 dv loop lsP HVdvP OKdvP2)|].
        eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errvQ) (r := dv) (a := adv) (OW := OWP) (LB := LB) (AD := AD) (EA := EA);
          [exact PREQ | reflexivity | exact HAdvP | reflexivity | reflexivity | unfold bn_dmax in *; lia]. }
      cbv beta. intros [uR lsR] stR msR [PO LEAFR]. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mS & OWR & -> & CPR & (-> & HDMR & _ & BLKR)).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENVQ CPR) as (ENVR & LSR).
      pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CPR) as RSR.
      cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 1152852)) with (Z_to_bv 64 1152852) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear PREQ CPR.
      (* [comment removed for export] *)
      destruct LEAFR as ((R1 & R2 & R3 & R4 & R5) & RD & _). cbn [snd] in *.
      pose proof (RSR _ _ HAdvP) as HAdvR. pose proof (RSR _ _ HArmP) as HArmR. pose proof (RSR _ _ HAnumP) as HAnumR. pose proof (RSR _ _ HAdvsP) as HAdvsR.
      pose proof (RSR _ _ HAtmpP) as HAtmpR. pose proof (RSR _ _ HAsnumP) as HAsnumR. pose proof (RSR _ _ HAsdivP) as HAsdivR.
      assert (GSR : getbn sdiv lsR = sd3) by (rewrite R1 by (apply NPd; exact NPdv); exact GSP).
      assert (GNR : getbn snum lsR = getbn snum lsP) by (apply R1, NPs; exact NPdv).
      assert (GnumR : getbn num lsR = bnum) by (rewrite R1 by exact NEdn; apply NPgP; exact NPnum).
      assert (GdvsR : getbn dvs lsR = bd) by (rewrite R1 by exact NEdd; apply NPgP; exact NPdvs).
      (* [comment removed for export] *)
      assert (HinsnR : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWR).
      { apply BLKR; [exact HinsnP|]. intros E.
        eapply (ids_bn_neq dv snum lsP psn psn (ids_m_nodup _ _ _ IDSP) HVdvP HVsnP (NPs dv NPdv) E Edsn). reflexivity. }
      clear BLKR RSR HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP ENVP LSP ENVQ LSQ NDP IDSP ADBP ERRBP SOKP HVsdP HVsnP HVdvP OKdvP2
            BNsdP BNsnP ARRsdP ARRsnP UsdP HinsP HinnP HinsnP.
      pose proof (RH_nodup_l _ _ _ _ (proj1 ENVR)) as NDR.
      destruct (lib_state_h_parts _ _ _ _ _ _ LSR) as (IDSR & ADBR & ERRBR & SOKR).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSR HAdvR) as HVdvR.
      destruct (lib_state_open [] lsR mS OWR AD EA num anum LSR NDR HAnumR ltac:(intros [])) as ((DnumR & BNnumR & _) & _ & _).
      destruct (lib_state_open [] lsR mS OWR AD EA dvs advs LSR NDR HAdvsR ltac:(intros [])) as ((DdvsR & BNdvsR & _) & _ & _).
      destruct (lib_state_open [] lsR mS OWR AD EA dv adv LSR NDR HAdvR ltac:(intros [])) as ((Ddv & BNdv & ARRdv) & (OKv1 & OKv2 & OKv3 & OKv4) & LSHR).
      rewrite GnumR in BNnumR. rewrite GdvsR in BNdvsR. unfold bn_cells in BNnumR, BNdvsR, BNdv.
      set (bv := getbn dv lsR) in *.
      destruct (ref_at_inb _ _ _ _ _ ADBR HAdvR) as (qv & Av & nv & _ & Hinv & Rv1 & Rv2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVR) Hinv) as (V0 & _ & _ & VC & VI).
      destruct (ref_at_inb _ _ _ _ _ ADBR HAnumR) as (qn & An & nn & _ & Hinn & Rn1 & Rn2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVR) Hinn) as (N0' & _ & _ & NC' & NI').
      destruct (ref_at_inb _ _ _ _ _ ADBR HAdvsR) as (qdR & AdR & ndR & _ & HindR & RdR1 & RdR2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVR) HindR) as (D0' & _ & _ & DC' & DI').
      (* [comment removed for export] *)
      assert (HDV : exists pv, bn_d bv = Some pv /\ In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWR).
      { unfold bn_arr in ARRdv. destruct (bn_d bv) as [pv|]; [exists pv; split; [reflexivity| exact (proj1 ARRdv)]|].
        exfalso. destruct ARRdv as [_ E]. unfold bn_dmax in RD. rewrite E in RD. cbn in RD. lia. }
      destruct HDV as (pv & Edv & Hinpv).
      pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVR) Hinpv) as (DVP & DV8).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVR) Hinpv) as (_ & _ & _ & DVC & _).
      pose proof (ref_at_ualign _ _ _ _ _ _ _ _ (proj1 ENVR) ADBR HAnumR) as (ANP & AN8).
      pose proof (ref_at_ualign _ _ _ _ _ _ _ _ (proj1 ENVR) ADBR HAdvsR) as (ADP & AD8).
      pose proof (ref_at_ualign _ _ _ _ _ _ _ _ (proj1 ENVR) ADBR HAdvR) as (AVP & AV8).
      assert (RDV : Ddv + 8 * Z.of_nat loop <= alloc_ceiling) by (clear - DVC RD; lia).
      env_open ENVR.
      match goal with MUx : munch _ mS mS |- _ => clear MUx end.
      pose proof (munch_refl [(bv_unsigned sp + -256, bv_unsigned sp); (adv, adv + 24)]%Z mS) as MUR.
      unfold MallocRep.wz in *. unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
      clear KZ.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      zstep. rewrite (land7 anum) by exact AN8.
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      zstep. rewrite (land7 advs) by exact AD8.
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      zstep. rewrite (land7 adv) by exact AV8.
      chk ltac:(fun C => clear - C; lia).
      step. rewrite (sx32_small (Z.b2z (bn_neg bnum))) by (destruct (bn_neg bnum); cbn; lia).
      step.
      step. rewrite (sx32_small (Z.b2z (bn_neg bd))) by (destruct (bn_neg bd); cbn; lia).
      zstep. step. zstep.
      setreg_at 10%Z (Z_to_bv 64 (Z.b2z (xorb (bn_neg bnum) (bn_neg bd)))) ltac:(f_equal; destruct (bn_neg bnum), (bn_neg bd); reflexivity).
      clear BNnumR BNdvsR NI' DI' SPI NPI N0' NC' D0' DC' Rn1 Rn2 RdR1 RdR2 SP0 SPC NP0 NPC RsP1 RsP2 RnP1 RnP2 DnumR DdvsR.
      do 2 zstep. rewrite ?land64_small by (clear - DVP RDV RLOOP CEIL LO SPR; lia).
      replace (0 <? Ddv) with true by (symmetry; apply Z.ltb_lt; exact DVP).
      replace (8 * Z.of_nat loop + Ddv <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DVP; lia).
      cbn [Z.b2z].
      step. step. step.
      chk ltac:(fun C => clear - C; lia).
      do 3 zstep.
      replace (8 * Z.of_nat loop + Ddv <? 8 * Z.of_nat loop) with false by (symmetry; apply Z.ltb_ge; clear - DVP; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      step. zstep.
      rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (unfold bn_dmax in *; lia).
      zstep. step. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
      ihere. to_implM. rewrite !bbind_get. rewrite GnumR, GdvsR. rewrite bbind_get_set. fold bv.
      set (q2 := mkBN (bn_d bv) (bn_buf bv) loop (xorb (bn_neg bnum) (bn_neg bd)) (bn_flags bv)).
      assert (WOKR : Forall (w_ok OWR LB lsR AD EA [dv]) [(bv_unsigned sp + -256, bv_unsigned sp); (adv, adv + 24)]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OWR LB lsR AD EA false [dv] _ dv adv); [left; reflexivity| exact HAdvR| cbn; lia| cbn; lia]| constructor]. }
      assert (HWLR : Forall (w_lib OWR lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp); (adv, adv + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (qv, Av, nv); cbn; auto| constructor]. }
      assert (LST : lib_state (setbn dv q2 lsR) mT OWR AD EA).
      { unfold lib_state. eapply (lib_state_close [] lsR mT OWR AD EA dv adv); [| exact NDR| exact HAdvR| | |].
        - match goal with HEAPx : RHEAP stR _ mS, WMx : wmono _ mS mT |- _ => exact (lib_state_frame stR LB [dv] lsR mS mT OWR AD EA _ HEAPx LSHR MUR WMx WOKR) end.
        - exists Ddv. split.
          + unfold bn_cells, q2, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. exact BNdv.
          + unfold bn_arr, q2 in *. cbn [bn_d bn_buf bn_dmax] in *. rewrite Edv in ARRdv |- *.
            destruct ARRdv as [Hin Uarr]. split; [exact Hin|].
            match goal with WMx : wmono _ mS mT |- _ => eapply u64arr_transport; [exact Uarr | exact MUR | exact WMx |] end.
            pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVR) Hin) as (_ & _ & _ & PC & _).
            pose proof (struct_limbs_disj stR OWR LB mS (proj1 ENVR) lsR AD EA IDSR ADBR dv dv adv pv Ddv _ HAdvR HVdvR Edv Hin) as SLD.
            cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax bv). lia.
        - unfold bn_okm, q2, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKv1|]. split; [exact RD|]. split; [exact OKv3| exact OKv4].
        - apply ids_ok_setbn_same; [exact IDSR| exact HVdvR| reflexivity]. }
      lazymatch type of ENVR with cenv ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j _ _ _ _ _ =>
        lazymatch goal with FRx : rw_cells _ mT (bv_unsigned sp + -256) ?fr' |- _ =>
          assert (ENVT : cenv a b c d e f g h i j fr' stR (setbn dv q2 lsR) mT OWR) end end.
      { apply cenv_setbn.
        match goal with FRx : rw_cells _ mT (bv_unsigned sp + -256) ?fr', STx : stk _ mT _ _, MIx : mem_inv _ mT, ERRx : rw_cells _ mT 3353076 _, WMx : wmono _ mS mT |- _ =>
          eapply (CSIL _ fr'); [exact ENVR | exact MUR | exact WMx | exact HWLR | exact STx | unfold LX_ERRNO, RATP; exact ERRx | exact MIx | exact FRx | cbn; lia] end. }
      set (lsT := setbn dv q2 lsR) in *.
      assert (HAtmpT : ref_at lsT OWR AD tmp atmp) by (apply ref_at_setbn; exact HAtmpR).
      destruct (lib_state_h_parts _ _ _ _ _ _ LST) as (IDST & _ & _ & SOKT).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LST HAtmpT) as HVtT.
      pose proof (st_okm_getbn tmp lsT SOKT HVtT) as (_ & OKtT2 & _).
      destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENVT LST ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errvT & PRET).
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply implM_embed_leaves; [apply (bn_wexpand_leaves2 tmp (dn + 1) lsT HVtT OKtT2)|].
        eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errvT) (r := tmp) (a := atmp) (OW := OWR) (LB := LB) (AD := AD) (EA := EA);
          [exact PRET | reflexivity | exact HAtmpT | reflexivity | f_equal; f_equal; lia | unfold bn_dmax in *; lia]. }
      cbv beta. intros [uU lsU] stU msU [PO LEAFU]. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mU & OWU & -> & CPU & (-> & HDMU & _ & BLKU)).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENVT CPU) as (ENVU & LSU).
      pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CPU) as RSU.
      cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 1152976)) with (Z_to_bv 64 1152976) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear PRET CPU.
      (* [comment removed for export] *)
      destruct LEAFU as ((U1 & U2 & U3 & U4 & U5) & UD & _). cbn [snd] in *.
      pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HAdvR)) as HAdvU. pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HArmR)) as HArmU.
      pose proof (RSU _ _ HAtmpT) as HAtmpU. pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HAsnumR)) as HAsnumU.
      pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HAsdivR)) as HAsdivU.
      assert (GSU : getbn sdiv lsU = sd3) by (rewrite U1 by exact NEtd; unfold lsT; rewrite getbn_setbn_other by (apply NPd; exact NPdv); exact GSR).
      assert (GNU : getbn snum lsU = getbn snum lsP) by (rewrite U1 by exact NEts; unfold lsT; rewrite getbn_setbn_other by (apply NPs; exact NPdv); exact GNR).
      assert (GVU : getbn dv lsU = q2) by (rewrite U1 by (apply not_eq_sym, NPt; exact NPdv); unfold lsT; apply getbn_setbn_same_m; exact HVdvR).
      assert (HinsnU : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWU).
      { apply BLKU; [exact HinsnR|]. intros E.
        assert (HVsT : valid_refm snum lsT) by (apply valid_refm_setbn; destruct snum; try exact I; apply (ref_at_valid _ _ _ _ _ _ _ _ LSR HAsnumR)).
        eapply (ids_bn_neq tmp snum lsT psn psn (ids_m_nodup _ _ _ IDST) HVtT HVsT NEts E); [|reflexivity].
        unfold lsT. rewrite getbn_setbn_other by (apply NPs; exact NPdv). rewrite GNR. exact Edsn. }
      assert (HinpvU : In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWU).
      { apply BLKU; [exact Hinpv|]. intros E.
        assert (HVvT : valid_refm dv lsT) by (apply valid_refm_setbn; exact HVdvR).
        eapply (ids_bn_neq tmp dv lsT pv pv (ids_m_nodup _ _ _ IDST) HVtT HVvT (fun E' => NPt dv NPdv (eq_sym E')) E); [|reflexivity].
        unfold lsT. rewrite getbn_setbn_same_m by exact HVdvR. exact Edv. }
      set (bsn := getbn snum lsP) in *.
      clear BLKU RSU HAdvR HArmR HAnumR HAdvsR HAtmpR HAsnumR HAsdivR HAtmpT ENVR LSR ENVT LST LSHR NDR IDSR ADBR ERRBR SOKR IDST SOKT HVtT OKtT2 HVdvR
            HinsnR Hinpv Hinv WOKR HWLR MUR BNdv ARRdv GSR GNR GnumR GdvsR R1 R2 R3 R4 R5 V0 VC VI Rv1 Rv2.
      assert (LOOP1 : (1 <= loop)%nat) by (unfold loop; lia).
      destruct (ref_at_inb _ _ _ _ _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LSU))) HAtmpU) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
      pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVU) Hint) as (T0' & _ & _ & TC' & _).
      env_open ENVU.
      unfold MallocRep.wz in *. unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
      clear KZ.
      pose proof (ref_at_ualign _ _ _ _ _ _ _ _ (proj1 ENVU) (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LSU))) HAtmpU) as (ATP & AT8).
      do 4 zstep. step. do 2 zstep. step. zstep. step. do 2 zstep. step. step. do 2 zstep. step.
      zstep.
      remember (Z_to_bv 64 4294967295) as mask32 eqn:Emask.
      step. subst mask32.
      zstep. step. do 2 zstep. step. step.
      (* [comment removed for export] *)
      pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVU) HinpvU) as (DVPu & DV8u).
      pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVU) HinsnU) as (SNPu & SN8u).
      replace (Z.land d1 4294967295) with (d1 mod 4294967296) in FRe0 by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
      rewrite (land7 Ddv) in FRe0 |- * by exact DV8u.
      rewrite (land7 DsnP) in FRe0 by exact SN8u.
      rewrite (land7 atmp) in FRe0 by exact AT8.
      rewrite (lxor_signbit63' (Z.of_nat dn)) in FRe0 by (clear - RDN; lia).
      replace (Z.of_nat dn + 9223372036854775808 <? 9223372036854775808) with false in FRe0 by (symmetry; apply Z.ltb_ge; clear; lia).
      replace (0 <? atmp) with true in FRe0 by (symmetry; apply Z.ltb_lt; exact ATP).
      change (0 <? 1) with true in FRe0. change (Z.b2z false) with 0 in FRe0. change (Z.b2z true) with 1 in FRe0. change (Z.land 1 1) with 1 in FRe0.
      replace (Z.of_nat dn ≪ 3) with (8 * Z.of_nat dn) in FRe0 |- * by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (DsnP + 8 * (Z.of_nat nP - 1)) with (DsnP + 8 * Z.of_nat (nP - 1)) in FRe0 by (clear - RNP; lia).
      replace (8 * Z.of_nat loop + Ddv) with (Ddv + 8 * Z.of_nat loop) by (clear; lia).
      env_close CSIL HWLs WOKs ENVU LSU ENVV LSV.
      ihere. to_implM.
      eapply (div_tail HM HF) with (dv := dv) (rm := rm) (tmp := tmp) (snum := snum) (sdiv := sdiv)
               (adv := adv) (arm := arm) (atmp := atmp) (asnum := asnum) (asdiv := asdiv) (psn := psn) (pv := pv) (sdbuf := nbuf) (negn := bn_neg bnum)
               (dn := dn) (loop := loop) (nP := nP) (d0 := d0) (d1 := d1) (sh := sh) (DsnP := DsnP) (Ddv := Ddv).
      { exact CEIL. }
      { exact GLO'. }
      { lia. }
      { exact SPB. }
      { exact ENVV. }
      { exact LSV. }
      { exact HAdvU. }
      { exact HArmU. }
      { exact HAtmpU. }
      { exact HAsnumU. }
      { exact HAsdivU. }
      { exact NEts. }
      { exact NEtd. }
      { exact NEsd. }
      { apply NPt. exact NPdv. }
      { apply NPs. exact NPdv. }
      { apply NPd. exact NPdv. }
      { rewrite GSU. reflexivity. }
      { rewrite GSU. exact C6b. }
      { exact HTOPD. }
      { reflexivity. }
      { reflexivity. }
      { exact (proj1 Rd0). }
      { rewrite GNU. exact TNP. }
      { unfold loop. lia. }
      { exact LOOP1. }
      { rewrite GNU. exact Edsn. }
      { rewrite GNU. exact HinsnU. }
      { rewrite GNU.
        apply (div_top_init (bn_buf bsn) (firstn tn (bn_buf bnum)) (firstn dn nbuf) sh dn tn nP).
        - exact OKp1.
        - rewrite <- TNP. exact OKp2.
        - exact HTOPD.
        - exact NP1.
        - exact NP2.
        - exact SH.
        - apply limbs_firstn. exact OKn1.
        - apply firstn_length_le. exact OKn2.
        - exact FNP.
        - apply limbs_firstn. exact LIMnb.
        - apply firstn_length_le. exact Lnb2.
        - rewrite nth_firstn. destruct (Nat.ltb_spec (dn - 1) dn); [exact (proj1 Rd0) | lia]. }
      { rewrite GVU. exact Edv. }
      { rewrite GVU. exact HinpvU. }
      { rewrite GVU. reflexivity. }
      { rewrite GVU. exact RD. }
      { exact UD. }
      { reflexivity. }
      { exact SH. } }
    unfold implM. iprefix.
    zstep. rewrite lts_signed by (unfold bn_dmax in *; lia). if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      ihere. to_implM.
      replace (tn + 1 <=? dn)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      unfold bbind at 1. unfold bret at 1. cbn [bind ret tree_ops tbind fst snd].
      eapply (CONT st8 ls8 _ OW8 (tn + 1)%nat); [exact ENV8' | exact LS8' | try eassumption; try lia ..].
      rewrite Nat.sub_diag. cbn [repeat]. rewrite app_nil_r. exact L8d.
    - (* [comment removed for export] *)
      ihere. to_implM.
      replace (tn + 1 <=? dn)%nat with true by (symmetry; apply Nat.leb_le; lia).
      lazymatch type of ENV8' with cenv _ _ _ _ _ _ _ _ _ _ ?FR8 _ _ _ _ =>
        split_cell FR8 (C8 (Z_to_bv 64 asnum)) ltac:(fun f1 rest =>
          split_cell rest (C8 (Z_to_bv 64 (Z.of_nat dn))) ltac:(fun f2 f3 =>
            lazymatch goal with |- implM _ (interp (embed (bbind _ _ ?REST0 _))) _ ?Q _ =>
              eapply (div_pad HM HF REST0 Q) with (snum := snum) (asnum := asnum) (dn := dn) (tnp := (tn + 1)%nat) (lo := lo) (B := B) (LB := LB) (AD := AD) (EA := EA)
                                                  (fr1 := f1) (fr2 := f2) (fr3 := f3)
            end))
      end.
      { exact CEIL. }
      { exact GLO'. }
      { lia. }
      { exact SPB. }
      { reflexivity. }
      { reflexivity. }
      { exact ENV8'. }
      { exact LS8'. }
      { exact HAsnum8. }
      { exact L8b. }
      { lia. }
      { unfold bn_dmax in *. lia. }
      intros stP lsP mP OWP q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVP LSP RSP OTH TOPP NEGP FNP.
      eapply (CONT stP lsP mP OWP (dn + 1)%nat); [exact ENVP | exact LSP | apply RSP; exact HAdv8 | apply RSP; exact HArm8 | apply RSP; exact HAnum8
        | apply RSP; exact HAdvs8 | apply RSP; exact HAtmp8 | apply RSP; exact HAsnum8 | apply RSP; exact HAsdiv8 | | | exact TOPP | lia | lia | left; lia | | ].
      + rewrite OTH by (intros E; apply NEsd; symmetry; exact E). exact Esd8.
      + intros r NP. rewrite OTH by (apply NPs; exact NP). apply NPget8. exact NP.
      + rewrite NEGP. exact L8c.
      + rewrite FNP, L8d. reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
