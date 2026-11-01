(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_W1_misc Fz_W1_ctrl Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_BIO_ctrl : Z := 0x236dbc.
Definition SITE_bc_ctrl : Z := 0x236f94.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition bc_frame (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bc_s0_post (sp gp tp t0 t2 a5 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' : word) (BI cmd larg parg lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1 : word) (mf : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bc_ctrl) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 larg)
               (Z_to_bv 64 BI) (Z_to_bv 64 cmd) (Z_to_bv 64 larg) (Z_to_bv 64 parg) (Z_to_bv 64 e_mem_ctrl) a5 (Z_to_bv 64 0) a7
               (Z_to_bv 64 parg) (Z_to_bv 64 cmd) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (BI + 8))
               (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_ctrl) fc None mf (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m mf /\ wmono asegs m mf /\ mem_inv asegs mf
    /\ rw_cells asegs mf (bv_unsigned sp + -96) (bc_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs mf lo (bv_unsigned sp + -96).

Lemma bc_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI cmd larg parg meth : Z),
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 64) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= cmd < 2^64 -> 0 <= larg < 2^64 -> 0 <= parg < 2^64 -> mem_inv asegs m ->
  evt asegs (bc_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t2 a5 a7 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' BI cmd larg parg lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 cmd) (Z_to_bv 64 larg) (Z_to_bv 64 parg) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp gp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6 F fc m lo BI cmd larg parg meth
    MethIs FrameRoom LoHigh SpTop StackM ImgClean ShadowBase Head BioAcc BioPos BioAlign BioHigh BioBelow MethSh CmdBits LargBits PargBits InvM.
  unfold bc_s0_post, e_BIO_ctrl, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as SpBits. unfold bv_modulus in SpBits. cbn [Z.of_N] in SpBits.
  remember (bv_unsigned sp) as U eqn:EU. rewrite <- (Z_to_bv_bv_unsigned sp), <- EU.
  pose proof (munch_refl [(U - 96, U)] m) as Untouched96. pose proof (wmono_refl asegs m) as Grow.
  assert (UtFoot : ut_fp [(U - 96, U)]) by ut_fp_lia. assert (ShFoot : sh_fp [(U - 96, U)]) by sh_fp_lia.
  assert (BioAl8 : BI mod 8 = 0) by (clear - BioAlign; Z.div_mod_to_equations; lia).
  assert (BioNZ : bv_eqb (Z_to_bv 64 BI) z64 = false).
  { unfold bv_eqb. rewrite (unsigned_lit BI) by lia. apply Z.eqb_neq. change (bv_unsigned z64) with 0. lia. }
  destruct MethIs as [-> | ->]; unfold bio_head, M_MEM_A, M_SECMEM_A in *;
  ( lazymatch type of MethSh with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MethSh end;
    th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat StackM;
    do 15 zstep; rewrite BioNZ; cbv iota;
    do 9 zstep; th_if_lit;
    do 40 (zstep; try th_if_lit);
    apply evt_done; exists t1, m1;
    split; [unfold SITE_bc_ctrl, e_mem_ctrl; reflexivity|];
    split; [exact Untouched96|]; split; [exact Grow|]; split; [exact InvM|];
    split; [unfold bc_frame; exact FR| exact StackM] ).
Qed.

(* [comment removed for export] *)
Definition bc_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 : word) (F : bvmap 5 word) (fc : bv 32) (v : word) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' v a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m (seg_rom asegs)
    /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m.

Lemma bc_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' v a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 (s1x s2x s3x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BI meth : Z),
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -96) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) (bc_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> mem_inv asegs m ->
  evt asegs (bc_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 F fc v lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x v a1 a2 a3 a4 a5 a6 a7 s2x s3x (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16))
             (Z_to_bv 64 (BI + 8)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bc_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' v a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 s1x s2x s3x F fc m lo BI meth
    MethIs FrameRoom LoHigh SpTop StackBelow ImgClean Saved Head BioAcc BioPos BioAlign BioHigh BioBelow InvM.
  unfold bc_s1_post, SITE_bc_ctrl in *. unfold bc_frame in Saved. unfold bio_head in Head.
  pose proof (bv_unsigned_in_range 64 sp) as SpBits. unfold bv_modulus in SpBits. cbn [Z.of_N] in SpBits.
  remember (bv_unsigned sp) as U eqn:EU. rewrite <- (Z_to_bv_bv_unsigned sp), <- EU.
  assert (BioAl8 : BI mod 8 = 0) by (clear - BioAlign; Z.div_mod_to_equations; lia).
  do 12 (zstep; try th_if_lit).
  do 14 zstep.
  th_release Saved U.
  apply evt_done. do 14 eexists. split; [reflexivity | split; [exact StackBelow | exact InvM]].
Qed.

Section CBctrl.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
(* [comment removed for export] *)
Hypothesis GO_memmeth : GOBJ MEM_METHOD 112.
(* [comment removed for export] *)
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.

Lemma memmeth_ctrl_sh : forall (Σ : rts RT) (m : mem), ART RT Σ m -> ro_cells asegs m ((MEM_METHOD + 64) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof using AFP GO_memmeth.
  intros Σ m Live.
  pose proof (afp_gsh_byte RT GOBJ AFP Σ m MEM_METHOD 112 (MEM_METHOD + 64) Live GO_memmeth) as Byte.
  unfold MEM_METHOD in *. exact (Byte ltac:(lia) ltac:(lia) eq_refl).
Qed.

Lemma meth_ctrl_sh : forall meth (Σ : rts RT) (m : mem), (meth = M_MEM_A \/ meth = M_SECMEM_A) -> ART RT Σ m ->
  ro_cells asegs m ((meth + 64) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof using AFP GO_memmeth GO_secmeth.
  intros meth Σ m Which Live.
  assert (Obj : GOBJ meth 112) by (destruct Which as [-> | ->]; [exact GO_memmeth | exact GO_secmeth]).
  assert (Slot : (meth + 64) mod 8 = 0) by (destruct Which as [-> | ->]; reflexivity).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ m meth 112 (meth + 64) Live Obj ltac:(lia) ltac:(lia) Slot) as Byte.
  replace (meth + 112 - (meth + 64)) with 48 in Byte by lia. exact Byte.
Qed.

(* [comment removed for export] *)
Definition bio_ctrl_info_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len off fl larg meth : Z) (iw shw rrw numw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 3 -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xba3ef0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  0 <= larg < 2 ^ 64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_ctrl m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (len - off)) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m') c).

Theorem bio_ctrl_info_cps : bio_ctrl_info_stmt.
Proof using AF AFP GO_memmeth GO_secmeth.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len off fl larg meth
    iw shw rrw numw padw rmaxw rflw OnlyFd Stable -> -> -> -> -> LiveBio BioAl MethIs HeadM W1M FlOk LiveBB BBAl BBM LiveBM BMAl LiveR RAl ReadM LargBits
    Rt0 Inv0 Call0 Deep T c Start Kont.
  destruct Call0 as (Stk0 & WinLo & RoomLo & TopSp & AlSp).
  pose proof (af_sp0_win RT AF Σ m Rt0) as Sp0Win.
  destruct (af_client_consts RT AF Σ m Rt0) as (_ & ShBase & _ & _ & Clean0).
  pose proof (af_live_range RT AF Σ m BI 128 Rt0 LiveBio) as (BioPos & BioTop & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 Rt0 LiveBio ltac:(lia)) as BioHi.
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 Rt0 LiveBio)) as BioAcc.
  pose proof (meth_ctrl_sh meth Σ m MethIs Rt0) as MethSh.
  pose proof (af_live_range RT AF Σ m BB 16 Rt0 LiveBB) as (_ & BBTop & _).
  pose proof (af_live_range RT AF Σ m R 32 Rt0 LiveR) as (_ & RTop & _).
  unfold RT_STACK, STACK_WIN, USTACK_TOP in WinLo, RoomLo, TopSp, Deep, BioTop, BBTop, RTop.
  assert (LoHi : 0x10007fff8000 <= lo) by lia.
  assert (Usp96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof (bc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI 3 larg 0 meth MethIs
                ltac:(lia) LoHi ltac:(lia) Stk0 Clean0 ShBase HeadM BioAcc BioPos BioAl BioHi
                ltac:(lia) MethSh ltac:(lia) LargBits ltac:(lia) Inv0) as Walk0.
  cl_lift Walk0 Start c1 AtCall.
  destruct (ASTA_unpack RT Σ _ _ c1 AtCall) as (ms1 & (t1q & m1 & -> & Out1 & Grow1 & Inv1 & Saved1 & Stk1) & At1). clear AtCall.
  assert (Rt1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] Rt0); [unfold STACK_WIN; lia | unfold USTACK_TOP; lia | exact Out1 | | exact Grow1].
    intros x NotOut. exfalso. apply NotOut. exact I. }
  assert (Below1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 96 -> rw_cells asegs m1 A cs).
  { intros A cs Cells Fits. apply (rw_cells_transport asegs _ m m1 A cs Cells Out1 Grow1). cbn [disjoint_from]. split; [left; exact Fits | exact I]. }
  pose proof (Below1 _ _ W1M ltac:(cbn [bio_w1_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as W1M1.
  pose proof (Below1 _ _ BBM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as BBM1.
  pose proof (Below1 _ _ ReadM ltac:(cbn [readp_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as ReadM1.
  pose proof (Below1 _ _ HeadM ltac:(cbn [bio_head cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HeadM1.
  assert (Call1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite Usp96. split; [exact Stk1|]. split; [unfold STACK_WIN; lia|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP; lia|].
    clear - AlSp. Z.div_mod_to_equations. lia. }
  refine (cps_realizes asegs _ _ T c1 (ctrl_info_cps RT AF GOBJ AFP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            F fc m1 lo BI BB BM R D len off fl iw shw rrw numw padw rmaxw rflw OnlyFd Stable eq_refl eq_refl eq_refl eq_refl
            LiveBio BioAl W1M1 FlOk LiveBB BBAl BBM1 LiveBM BMAl LiveR RAl ReadM1 Rt1 Inv1 Call1) At1 _).
  intros c2 Back.
  destruct (ASTA_unpack RT Σ _ _ c2 Back) as (ms2 & (m2 & Ret2 & After2 & Kept2) & At2). clear Back.
  rewrite Usp96 in After2, Kept2. destruct After2 as (Rt2 & Inv2 & Grow2 & Stk2).
  destruct Ret2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_bc_ctrl ltac:(unfold SITE_bc_ctrl; lia) eq_refl) in At2.
  destruct (af_client_consts RT AF Σ m2 Rt2) as (_ & _ & _ & _ & Clean2).
  pose proof (proj2 (af_acc_live RT AF Σ m2 BI 128 Rt2 LiveBio)) as BioAcc2.
  assert (Saved2 : rw_cells asegs m2 (bv_unsigned sp + -96) (bc_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ Saved1). intros a InFrame.
    cbn [bc_frame cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in InFrame.
    apply Kept2. apply acl_stack. unfold USTACK_TOP. lia. }
  assert (Head2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ HeadM1). intros a InHead.
    cbn [bio_head cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in InHead.
    apply Kept2. apply (acl_live _ _ _ BI 128); [exact LiveBio | lia]. }
  pose proof (bc_s1_walk ra (Z_to_bv 64 SITE_bc_ctrl) sp gp u0 u1 u2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (len - off)) b1 b2 b3 b4 b5 b6 b7
                s11 u3 u4 u5 u6 (Z_to_bv 64 larg) (Z_to_bv 64 0) (Z_to_bv 64 3) F2 fc2 m2 lo BI meth MethIs
                ltac:(lia) LoHi ltac:(lia) Stk2 Clean2 Saved2 Head2 BioAcc2 BioPos BioAl BioHi ltac:(lia) Inv2) as Walk2.
  cl_lift Walk2 At2 c3 AtRet.
  apply Kont. eapply ASTA_conseq; [exact AtRet|].
  intros ms (k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & -> & StkEnd & InvEnd).
  exists m2. split; [unfold ret_st; do 16 eexists; reflexivity|].
  split; [exact (conj Rt2 (conj Inv2 (conj (wmono_trans asegs _ _ _ Grow1 Grow2) StkEnd)))|].
  intros a Client.
  assert (Client96 : aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -96) (bv_unsigned a))
    by (apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)); [exact Client | auto | auto | lia]).
  rewrite (Kept2 a Client96).
  apply Out1. cbn [outside]. split; [| exact I].
  destruct (cl_split RT AF Σ m (bv_unsigned sp) 96 (bv_unsigned a) Rt0 ltac:(unfold STACK_WIN; lia) ltac:(lia) Client); lia.
Qed.

(* [comment removed for export] *)
Definition bio_ctrl_ptr_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl iw PP larg meth : Z) (shw rrw numw padw rmaxw flw oldpp : word) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 PP -> tp = Z_to_bv 64 0xba3ef0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw flw) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> 0 < max < 2 ^ 31 -> length junk = Z.to_nat max -> rw_cells asegs m D [CB (Z.to_nat max) junk] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP ->
  0 <= larg < 2 ^ 64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_ctrl m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists rmaxw' m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (CP_W BM R D max PP) m m'
        /\ rw_cells asegs m' BM (bufmem_cells (len - off) D max flw)
        /\ rw_cells asegs m' R (readp_cells (len - off) D 0 rmaxw' flw)
        /\ rw_cells asegs m' D [CB (Z.to_nat max) (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))]
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)]) c).

Theorem bio_ctrl_ptr_cps : bio_ctrl_ptr_stmt.
Proof using AF AFP MMV GO_memmeth GO_secmeth.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl iw PP larg meth
    shw rrw numw padw rmaxw flw oldpp junk OnlyFd Stable -> -> -> -> -> LiveBio BioAl MethIs HeadM W1M FlOk IwBits LiveBB BBAl BBM LiveBM BMAl BufM
    LiveR RAl ReadM NeMR LiveD NeDI NeDB NeDM NeDR OffLen LenMax MaxBits LenJunk DataM PPAl SlotM PPAt LargBits Rt0 Inv0 Call0 Deep T c Start Kont.
  destruct Call0 as (Stk0 & WinLo & RoomLo & TopSp & AlSp).
  pose proof (pp_facts RT AF Σ m (bv_unsigned sp) lo PP Rt0 PPAt PPAl WinLo RoomLo TopSp)
    as (PPPos & PPTop & _ & _ & PPStk & _ & PPApart & _).
  pose proof (af_sp0_win RT AF Σ m Rt0) as Sp0Win.
  destruct (af_client_consts RT AF Σ m Rt0) as (_ & ShBase & _ & _ & Clean0).
  pose proof (af_live_range RT AF Σ m BI 128 Rt0 LiveBio) as (BioPos & BioTop & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 Rt0 LiveBio ltac:(lia)) as BioHi.
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 Rt0 LiveBio)) as BioAcc.
  pose proof (meth_ctrl_sh meth Σ m MethIs Rt0) as MethSh.
  pose proof (af_live_range RT AF Σ m BB 16 Rt0 LiveBB) as (_ & BBTop & _).
  pose proof (af_live_range RT AF Σ m BM 32 Rt0 LiveBM) as (_ & BMTop & _).
  pose proof (af_live_range RT AF Σ m R 32 Rt0 LiveR) as (_ & RTop & _).
  pose proof (af_live_range RT AF Σ m D max Rt0 LiveD) as (_ & DTop & _).
  unfold RT_STACK, STACK_WIN, USTACK_TOP in WinLo, RoomLo, TopSp, Deep, BioTop, BBTop, BMTop, RTop, DTop.
  assert (LoHi : 0x10007fff8000 <= lo) by lia.
  assert (Usp96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof (bc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI 115 larg PP meth MethIs
                ltac:(lia) LoHi ltac:(lia) Stk0 Clean0 ShBase HeadM BioAcc BioPos BioAl BioHi
                ltac:(lia) MethSh ltac:(lia) LargBits ltac:(lia) Inv0) as Walk0.
  cl_lift Walk0 Start c1 AtCall.
  destruct (ASTA_unpack RT Σ _ _ c1 AtCall) as (ms1 & (t1q & m1 & -> & Out1 & Grow1 & Inv1 & Saved1 & Stk1) & At1). clear AtCall.
  assert (Rt1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] Rt0); [unfold STACK_WIN; lia | unfold USTACK_TOP; lia | exact Out1 | | exact Grow1].
    intros x NotOut. exfalso. apply NotOut. exact I. }
  assert (Away1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= A -> rw_cells asegs m1 A cs).
  { intros A cs Cells Fits. apply (rw_cells_transport asegs _ m m1 A cs Cells Out1 Grow1). cbn [disjoint_from]. split; [exact Fits | exact I]. }
  pose proof (Away1 _ _ W1M ltac:(cbn [bio_w1_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as W1M1.
  pose proof (Away1 _ _ BBM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as BBM1.
  pose proof (Away1 _ _ BufM ltac:(cbn [bufmem_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as BufM1.
  pose proof (Away1 _ _ ReadM ltac:(cbn [readp_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as ReadM1.
  pose proof (Away1 _ _ HeadM ltac:(cbn [bio_head cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HeadM1.
  pose proof (Away1 _ _ SlotM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PPStk RoomLo; lia)) as SlotM1.
  pose proof (Away1 _ _ DataM ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)) as DataM1.
  assert (Call1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite Usp96. split; [exact Stk1|]. split; [unfold STACK_WIN; lia|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP; lia|].
    clear - AlSp. Z.div_mod_to_equations. lia. }
  assert (PPAt1 : pp_loc (rt_frames RT Σ) m1 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) PP).
  { rewrite Usp96. destruct PPAt as [(AboveSp & BelowTop) | (f & k & InFrames & FLo & FHi & ShadowZero)].
    - left. lia.
    - right. exists f, k. split; [exact InFrames|]. split; [exact FLo|]. split; [exact FHi|].
      apply (bytes_at_transport asegs _ m m1 _ _ ShadowZero Out1). cbn [disjoint_from length Z.of_nat Pos.of_succ_nat]. split; [left | exact I].
      assert (PP / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold shad, SHB. lia. }
  assert (Deep1 : lo + RT_STACK + 144 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) by (rewrite Usp96; unfold RT_STACK; lia).
  refine (cps_realizes asegs _ _ T c1 (ctrl_ptr_cps RT AF GOBJ AFP MMV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            F fc m1 lo BI BB BM R D len max off fl iw PP shw rrw numw padw rmaxw flw oldpp junk OnlyFd Stable eq_refl eq_refl eq_refl eq_refl
            LiveBio BioAl W1M1 FlOk IwBits LiveBB BBAl BBM1 LiveBM BMAl BufM1 LiveR RAl ReadM1 LiveD MaxBits OffLen LenMax DataM1 LenJunk
            NeDB NeDM NeDR NeMR PPAl SlotM1 PPAt1 Rt1 Inv1 Call1 Deep1) At1 _).
  intros c2 Back.
  destruct (ASTA_unpack RT Σ _ _ c2 Back) as (ms2 & (rmaxw2 & m2 & Ret2 & After2 & Kept2 & BufM2 & ReadM2 & DataM2 & SlotM2) & At2). clear Back.
  rewrite Usp96 in After2, Kept2. destruct After2 as (Rt2 & Inv2 & Grow2 & Stk2).
  destruct Ret2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_bc_ctrl ltac:(unfold SITE_bc_ctrl; lia) eq_refl) in At2.
  destruct (af_client_consts RT AF Σ m2 Rt2) as (_ & _ & _ & _ & Clean2).
  pose proof (proj2 (af_acc_live RT AF Σ m2 BI 128 Rt2 LiveBio)) as BioAcc2.
  assert (Saved2 : rw_cells asegs m2 (bv_unsigned sp + -96) (bc_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ Saved1). intros a InFrame.
    cbn [bc_frame cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in InFrame.
    apply Kept2; [apply acl_stack; unfold USTACK_TOP; lia |]. cbn [outside].
    clear - InFrame PPStk BMTop RTop DTop WinLo RoomLo. lia. }
  assert (Head2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ HeadM1). intros a InHead.
    cbn [bio_head cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in InHead.
    apply Kept2; [apply (acl_live _ _ _ BI 128); [exact LiveBio | lia] |]. cbn [outside].
    pose proof (live_ne_apart RT AF Σ m BI 128 BM 32 Rt0 LiveBio LiveBM ltac:(intro Same; injection Same; lia)) as BioVsBuf.
    pose proof (live_ne_apart RT AF Σ m BI 128 R 32 Rt0 LiveBio LiveR ltac:(intro Same; injection Same; lia)) as BioVsRead.
    pose proof (live_ne_apart RT AF Σ m BI 128 D max Rt0 LiveBio LiveD ltac:(intro Same; injection Same; intros; apply NeDI; lia)) as BioVsData.
    pose proof (PPApart BI 128 LiveBio) as BioVsSlot.
    clear - InHead BioVsBuf BioVsRead BioVsData BioVsSlot. lia. }
  pose proof (bc_s1_walk ra (Z_to_bv 64 SITE_bc_ctrl) sp gp u0 u1 u2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7
                s11 u3 u4 u5 u6 (Z_to_bv 64 larg) (Z_to_bv 64 PP) (Z_to_bv 64 115) F2 fc2 m2 lo BI meth MethIs
                ltac:(lia) LoHi ltac:(lia) Stk2 Clean2 Saved2 Head2 BioAcc2 BioPos BioAl BioHi ltac:(lia) Inv2) as Walk2.
  cl_lift Walk2 At2 c3 AtRet.
  apply Kont. eapply ASTA_conseq; [exact AtRet|].
  intros ms (k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & -> & StkEnd & InvEnd).
  exists rmaxw2, m2. split; [unfold ret_st; do 16 eexists; reflexivity|].
  split; [exact (conj Rt2 (conj Inv2 (conj (wmono_trans asegs _ _ _ Grow1 Grow2) StkEnd)))|].
  split.
  - intros a Client Outs.
    assert (Client96 : aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -96) (bv_unsigned a))
      by (apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)); [exact Client | auto | auto | lia]).
    rewrite (Kept2 a Client96 Outs).
    apply Out1. cbn [outside]. split; [| exact I].
    destruct (cl_split RT AF Σ m (bv_unsigned sp) 96 (bv_unsigned a) Rt0 ltac:(unfold STACK_WIN; lia) ltac:(lia) Client); lia.
  - split; [exact BufM2|]. split; [exact ReadM2|]. split; [exact DataM2 | exact SlotM2].
Qed.
(* [comment removed for export] *)
Definition bio_ctrl_ptr_same_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R fl iw PP larg meth : Z) (shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp : word),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 PP -> tp = Z_to_bv 64 0xba3ef0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 lw; C8 dw; C8 mw; C8 flw] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R [C8 rlw; C8 dw; C8 rmw; C8 rflw] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP ->
  0 <= larg < 2 ^ 64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_ctrl m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(PP, PP + 8)] m m'
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)]) c).

Theorem bio_ctrl_ptr_same_cps : bio_ctrl_ptr_same_stmt.
Proof using AF AFP GO_memmeth GO_secmeth.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R fl iw PP larg meth
    shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp OnlyFd Stable -> -> -> -> -> LiveBio BioAl MethIs HeadM W1M FlOk IwBits LiveBB BBAl BBM
    LiveBM BMAl BufM LiveR RAl ReadM PPAl SlotM PPAt LargBits Rt0 Inv0 Call0 Deep T c Start Kont.
  destruct Call0 as (Stk0 & WinLo & RoomLo & TopSp & AlSp).
  pose proof (pp_facts RT AF Σ m (bv_unsigned sp) lo PP Rt0 PPAt PPAl WinLo RoomLo TopSp)
    as (PPPos & PPTop & _ & _ & PPStk & _ & PPApart & _).
  pose proof (af_sp0_win RT AF Σ m Rt0) as Sp0Win.
  destruct (af_client_consts RT AF Σ m Rt0) as (_ & ShBase & _ & _ & Clean0).
  pose proof (af_live_range RT AF Σ m BI 128 Rt0 LiveBio) as (BioPos & BioTop & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 Rt0 LiveBio ltac:(lia)) as BioHi.
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 Rt0 LiveBio)) as BioAcc.
  pose proof (meth_ctrl_sh meth Σ m MethIs Rt0) as MethSh.
  pose proof (af_live_range RT AF Σ m BB 16 Rt0 LiveBB) as (_ & BBTop & _).
  pose proof (af_live_range RT AF Σ m BM 32 Rt0 LiveBM) as (_ & BMTop & _).
  pose proof (af_live_range RT AF Σ m R 32 Rt0 LiveR) as (_ & RTop & _).
  unfold RT_STACK, STACK_WIN, USTACK_TOP in WinLo, RoomLo, TopSp, Deep, BioTop, BBTop, BMTop, RTop.
  assert (LoHi : 0x10007fff8000 <= lo) by lia.
  assert (Usp96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof (bc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI 115 larg PP meth MethIs
                ltac:(lia) LoHi ltac:(lia) Stk0 Clean0 ShBase HeadM BioAcc BioPos BioAl BioHi
                ltac:(lia) MethSh ltac:(lia) LargBits ltac:(lia) Inv0) as Walk0.
  cl_lift Walk0 Start c1 AtCall.
  destruct (ASTA_unpack RT Σ _ _ c1 AtCall) as (ms1 & (t1q & m1 & -> & Out1 & Grow1 & Inv1 & Saved1 & Stk1) & At1). clear AtCall.
  assert (Rt1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] Rt0); [unfold STACK_WIN; lia | unfold USTACK_TOP; lia | exact Out1 | | exact Grow1].
    intros x NotOut. exfalso. apply NotOut. exact I. }
  assert (Away1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= A -> rw_cells asegs m1 A cs).
  { intros A cs Cells Fits. apply (rw_cells_transport asegs _ m m1 A cs Cells Out1 Grow1). cbn [disjoint_from]. split; [exact Fits | exact I]. }
  pose proof (Away1 _ _ W1M ltac:(cbn [bio_w1_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as W1M1.
  pose proof (Away1 _ _ BBM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as BBM1.
  pose proof (Away1 _ _ BufM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as BufM1.
  pose proof (Away1 _ _ ReadM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as ReadM1.
  pose proof (Away1 _ _ HeadM ltac:(cbn [bio_head cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HeadM1.
  pose proof (Away1 _ _ SlotM ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PPStk RoomLo; lia)) as SlotM1.
  assert (Call1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite Usp96. split; [exact Stk1|]. split; [unfold STACK_WIN; lia|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP; lia|].
    clear - AlSp. Z.div_mod_to_equations. lia. }
  assert (PPAt1 : pp_loc (rt_frames RT Σ) m1 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) PP).
  { rewrite Usp96. destruct PPAt as [(AboveSp & BelowTop) | (f & k & InFrames & FLo & FHi & ShadowZero)].
    - left. lia.
    - right. exists f, k. split; [exact InFrames|]. split; [exact FLo|]. split; [exact FHi|].
      apply (bytes_at_transport asegs _ m m1 _ _ ShadowZero Out1). cbn [disjoint_from length Z.of_nat Pos.of_succ_nat]. split; [left | exact I].
      assert (PP / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold shad, SHB. lia. }
  assert (Deep1 : lo + RT_STACK + 144 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) by (rewrite Usp96; unfold RT_STACK; lia).
  refine (cps_realizes asegs _ _ T c1 (ctrl_ptr_same_cps RT AF GOBJ AFP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            F fc m1 lo BI BB BM R fl iw PP shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp OnlyFd Stable eq_refl eq_refl eq_refl eq_refl
            LiveBio BioAl W1M1 FlOk IwBits LiveBB BBAl BBM1 LiveBM BMAl BufM1 LiveR RAl ReadM1 PPAl SlotM1 PPAt1 Rt1 Inv1 Call1 Deep1) At1 _).
  intros c2 Back.
  destruct (ASTA_unpack RT Σ _ _ c2 Back) as (ms2 & (m2 & Ret2 & After2 & Kept2 & SlotM2) & At2). clear Back.
  rewrite Usp96 in After2, Kept2. destruct After2 as (Rt2 & Inv2 & Grow2 & Stk2).
  destruct Ret2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_bc_ctrl ltac:(unfold SITE_bc_ctrl; lia) eq_refl) in At2.
  destruct (af_client_consts RT AF Σ m2 Rt2) as (_ & _ & _ & _ & Clean2).
  pose proof (proj2 (af_acc_live RT AF Σ m2 BI 128 Rt2 LiveBio)) as BioAcc2.
  assert (Saved2 : rw_cells asegs m2 (bv_unsigned sp + -96) (bc_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ Saved1). intros a InFrame.
    cbn [bc_frame cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in InFrame.
    apply Kept2; [apply acl_stack; unfold USTACK_TOP; lia |]. cbn [outside].
    clear - InFrame PPStk RoomLo. lia. }
  assert (Head2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ HeadM1). intros a InHead.
    cbn [bio_head cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in InHead.
    apply Kept2; [apply (acl_live _ _ _ BI 128); [exact LiveBio | lia] |]. cbn [outside].
    pose proof (PPApart BI 128 LiveBio) as BioVsSlot. clear - InHead BioVsSlot. lia. }
  pose proof (bc_s1_walk ra (Z_to_bv 64 SITE_bc_ctrl) sp gp u0 u1 u2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7
                s11 u3 u4 u5 u6 (Z_to_bv 64 larg) (Z_to_bv 64 PP) (Z_to_bv 64 115) F2 fc2 m2 lo BI meth MethIs
                ltac:(lia) LoHi ltac:(lia) Stk2 Clean2 Saved2 Head2 BioAcc2 BioPos BioAl BioHi ltac:(lia) Inv2) as Walk2.
  cl_lift Walk2 At2 c3 AtRet.
  apply Kont. eapply ASTA_conseq; [exact AtRet|].
  intros ms (k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & -> & StkEnd & InvEnd).
  exists m2. split; [unfold ret_st; do 16 eexists; reflexivity|].
  split; [exact (conj Rt2 (conj Inv2 (conj (wmono_trans asegs _ _ _ Grow1 Grow2) StkEnd)))|].
  split; [| exact SlotM2].
  intros a Client Outs.
  assert (Client96 : aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -96) (bv_unsigned a))
    by (apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)); [exact Client | auto | auto | lia]).
  rewrite (Kept2 a Client96 Outs).
  apply Out1. cbn [outside]. split; [| exact I].
  destruct (cl_split RT AF Σ m (bv_unsigned sp) 96 (bv_unsigned a) Rt0 ltac:(unfold STACK_WIN; lia) ltac:(lia) Client); lia.
Qed.
End CBctrl.
