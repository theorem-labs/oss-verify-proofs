(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/ZBridge.v; 287 of its 304 lines of code are new or changed and 392 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top.
Import ListNotations.
Open Scope Z_scope.

Ltac c1_off E :=
  match E with
  | Z.add ?X ?c => let c' := zlit c in let d := c1_off X in eval vm_compute in (d + c')%Z
  | _ => constr:(0%Z)
  end.

Ltac c1_base E :=
  match E with
  | Z.add ?X ?c => let c' := zlit c in c1_base X
  | _ => E
  end.

Ltac addr_diff E A ::=
  match constr:(tt) with
  | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
  | _ =>
      let bE := c1_base E in let bA := c1_base A in
      lazymatch bA with
      | bE => let oE := c1_off E in let oA := c1_off A in eval vm_compute in (oE - oA)%Z
      end
  end.

Ltac c1_unlit :=
  repeat match goal with
  | |- context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_lit z) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit_wrap z)
  end.

Ltac c1_dec :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by mlia | rewrite (proj2 (Z.eqb_neq x y)) by mlia ]
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by mlia | rewrite (proj2 (Z.ltb_ge x y)) by mlia ]
  | |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by mlia | rewrite (proj2 (Z.leb_gt x y)) by mlia ]
  end.

Ltac c1_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu, v_slti, v_sltiu, v_slt, v_sltu, c_lts, c_ltu, zsig;
  c1_unlit; c1_dec; reflexivity.

Ltac c1_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by (symmetry; c1_cond); cbv iota
            | replace c with false by (symmetry; c1_cond); cbv iota ]
  end.

Lemma c1_le1z : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Ltac c1_st := step; try (rewrite c1_le1z; mem_after_store).

Lemma c1_ret : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H1 H2. apply ret_pc_even; assumption. Qed.

Ltac c1_retpc :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => rewrite (c1_ret n) by first [lia | reflexivity]
  end.

Ltac sg_br H := if_cases H; cbv iota.

Lemma rd_head : forall m Q x l, bytes_at rsegs m Q (x :: l) ->
  ov_read_bytes rsegs m (Z_to_bv 64 Q) 1 = Some [x] /\ bytes_at rsegs m (Q + 1) l.
Proof.
  intros m Q x l H. change (x :: l) with ([x] ++ l) in H. apply bytes_at_app in H as [H1 H2]. split.
  - pose proof (bytes_at_ov_read rsegs m Q [x] 0 1 H1 ltac:(cbn; lia)) as E.
    cbn [Z.of_nat firstn skipn] in E. rewrite Z.add_0_r in E. exact E.
  - cbn [length] in H2. replace (Q + Z.of_nat 1) with (Q + 1) in H2 by lia. exact H2.
Qed.

Ltac rd_prep :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    match goal with
    | HP : bytes_at segs m ?Q (?x :: ?l) |- _ =>
        let HR := fresh "HR" in let HP' := fresh "HP" in
        destruct (rd_head m Q x l HP) as [HR HP']; clear HP
    end
  end.

Ltac rd_go lbu stop :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              tryif constr_eq pc stop then fail
              else (tryif constr_eq pc lbu then (rd_prep; step) else step)
          end;
          try c1_if; try (rewrite c1_le1z; mem_after_store); try (rewrite le1_zxb; mem_after_store)).

Ltac rd_m6 H HM :=
  match type of H with
  | ?P ?segs ?m ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?x0 :: ?x1 :: ?x2 :: ?post) =>
      let n := eval vm_compute in (cells_size [x0; x1; x2]) in
      lazymatch n with
      | 6%nat => pose proof (rw_cells_merge segs m A [c0; c1; c2; c3] [x0; x1; x2] post H) as HM
      end
  | ?P ?segs ?m ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?post) =>
      let n := eval vm_compute in (cells_size [x0; x1; x2; x3; x4; x5]) in
      lazymatch n with
      | 6%nat => pose proof (rw_cells_merge segs m A [c0; c1; c2; c3] [x0; x1; x2; x3; x4; x5] post H) as HM
      end
  end;
  cbn [app cells_size csize Nat.add cells_bytes cbytes] in HM.

Definition llvm_case_Q (sp gp tp s0 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo r fab i e q0 : Z) (bs : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word)
      (m' : word -> option byte) (j0 j1 jm : list byte) (q c : Z) (bs' : list byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 0x13440) fc None m' (seg_rom rsegs) /\
    s3' = Z_to_bv 64 4294967295 /\ s6' = Z_to_bv 64 1 /\ s7' = Z_to_bv 64 fab /\
    munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp)
      [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
       CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] /\
    q0 <= q /\ 0 <= c /\ q + c = e /\
    bytes_at rsegs m' r bs' /\ wr_at rsegs m' r 288 /\ boxreg_inv bs' /\ bx_fabric bs' = fab /\
    llvm_kept bs bs' (-1).

Definition llvm_case_evt (pc0 : Z) : Prop :=
  forall (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte)
         (spv lo r fab ip inn op i e : Z) (gp tp : word) (j0 j1 jm bs rest : list byte),
    getr regs 2 = Z_to_bv 64 spv -> getr regs 3 = gp -> getr regs 4 = tp -> getr regs 8 = Z_to_bv 64 r ->
    getr regs 9 = Z_to_bv 64 op -> getr regs 18 = Z_to_bv 64 inn -> getr regs 19 = Z_to_bv 64 (ip + 1) ->
    getr regs 20 = Z_to_bv 64 ip -> getr regs 21 = Z_to_bv 64 (inn - 1) -> getr regs 22 = Z_to_bv 64 1 ->
    getr regs 23 = Z_to_bv 64 fab -> getr regs 24 = Z_to_bv 64 (-1 - (spv + 48)) ->
    getr regs 25 = Z_to_bv 64 (-1 - r) -> getr regs 26 = Z_to_bv 64 (spv + 48) -> getr regs 27 = Z_to_bv 64 336 ->
    rw_cells rsegs mem spv
      [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
       CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (inn - 1))] ->
    rw_cells rsegs mem r [CB 288 bs] -> boxreg_inv bs -> bx_fabric bs = fab ->
    bytes_at rsegs mem (ip + 1) rest -> Z.of_nat (length rest) = inn - 1 ->
    mem_inv rsegs mem -> stk rsegs mem lo spv ->
    LF_RES_TOP <= lo -> lo + 144 <= spv -> spv + 464 <= 2 ^ 47 -> spv mod 16 = 0 ->
    4096 <= r -> r mod 16 = 0 -> r + 288 <= lo -> 0 <= ip -> ip + inn = e -> e <= lo -> 1 <= inn -> inn < 2 ^ 26 ->
    0 <= op < 256 -> 0 <= i <= 63 ->
    evt rsegs (llvm_case_Q (Z_to_bv 64 spv) gp tp (Z_to_bv 64 r) (Z_to_bv 64 (-1 - (spv + 48))) (Z_to_bv 64 (-1 - r))
                 (Z_to_bv 64 (spv + 48)) (Z_to_bv 64 336) F fc mem lo r fab i e ip bs)
      (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 pc0) fc None mem (seg_rom rsegs)).

Lemma sg_byte : forall m a v, 0 <= a -> a + 1 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 1 = Some [v] -> bytes_at rsegs m a [v].
Proof.
  intros m a v Ha Ha1 Hv. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj.
  assert (j = 0%nat) by lia. subst j. cbn [nth_error]. rewrite Z.add_0_r. unfold wa.
  rewrite PropExec.ov_rdn in Hv. cbn [PropExec.rdn] in Hv. unfold mrd.
  destruct (m (Z_to_bv 64 a)) as [x|]; [injection Hv as ->; reflexivity|].
  destruct (PropExec.seg_rom rsegs (Z_to_bv 64 a)) as [x|]; [injection Hv as ->; reflexivity | discriminate].
Qed.

Lemma sg_list : forall m c a, 0 <= a -> a + Z.of_nat c <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat c -> exists v, ov_read_bytes rsegs m (Z_to_bv 64 x) 1 = Some [v]) ->
  exists l, length l = c /\ bytes_at rsegs m a l.
Proof.
  intros m c. induction c as [|c IH]; intros a Ha Hc H.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - destruct (H a ltac:(lia)) as [v Hv].
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply H; lia)) as (l & Hl & Hb).
    exists (v :: l). split; [cbn; lia|].
    change (v :: l) with ([v] ++ l). apply bytes_at_app. split; [apply sg_byte; [lia | lia | exact Hv]|].
    cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact Hb.
Qed.

Lemma sg_rw_mk : forall m A bs, bytes_at rsegs m A bs -> length bs = 288%nat -> wr_at rsegs m A 288 ->
  rw_cells rsegs m A [CB 288 bs].
Proof.
  intros m A bs HB HL HW. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - exact HW.
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma llvm_alloc_mem : forall stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md r k mem' W,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  llvm_alloc B API stk L0 A0 regs0 mem0 md0 b L A mem md r k ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> spZ regs0 - stk <= x < spZ regs0 \/ r <= x < r + 288) ->
  llvm_alloc B API stk L0 A0 regs0 mem0 md0 b L A mem' md r k.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md r k mem' W CTX (FR & MINE & RES) MU WM Hro HW.
  pose proof CTX as (BI & Hk0 & _ & Hpre & _).
  pose proof BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & Hceil & H63 & _).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold LLVM_K, LLVM_FRAME in Hk0.
  split; [|split; [exact MINE | exact RES]].
  eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | lia | lia | exact MU | exact WM | exact Hro |].
  intros x Hx NO. destruct (HW x Hx NO) as [H|H]; [left; exact H|].
  right. exists r, 288. split; [exact MINE | lia].
Qed.

Theorem llvm_case_of_evt : forall op3, llvm_case_evt (llvm_case_pc op3) -> llvm_case_ok B API op3.
Proof.
  intros op3 EV stk empty L0 A0 regs0 mem0 md0 ra p n b i k c CTX HT (ms & mdx & Ec & Epc).
  pose proof CTX as (BI & Hk0 & Hra & Hpre & Hsn & H47 & Hres0 & Hroom & Hro0 & Hgi & Hfrm0 & Hn26).
  pose proof BI as (SEGS & _ & _ & HGG & _ & AX).
  destruct HT as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & op & j0 & j1 & jm & Ec' & Hfrm & RB &
    E9 & E18 & E19 & E20 & E21 & FRC & Hi & Hinn & Hip & Hipn & Hop & RWR & INV & Hfab & AL & Hk).
  rewrite Ec' in Ec. injection Ec as Ems Emd. subst ms mdx. unfold YK11.mkst in Epc. cbn [ms_pc_val] in Epc.
  subst c. rewrite Epc.
  pose proof AL as (FR & MINE & RES).
  destruct RB as (E2 & E3 & E4 & E8 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold LLVM_K, LLVM_FRAME in Hk0.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  pose proof INV as ((Lbs & B1 & _) & _).
  pose proof MINE as (Hin & _ & _).
  apply blocks_In in Hin as (q0 & Hq0 & Hq0in).
  pose proof (mr_blocks_aligned B _ (aa_laws API) L A mem md q0 288 HM Hq0in) as Hr16.
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q0 288 HM Hq0in) as Hrr.
  rewrite Hq0 in Hr16, Hrr.
  assert (Hpn : 4096 <= p /\ p + n <= spZ regs0 - stk).
  { destruct Hpl as [[En _] | [Hn (q & Hq & Hqp)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM0 Hq ltac:(lia)) as (_ & H1 & H2 & _).
    rewrite Hqp in H1, H2. lia. }
  assert (Hrimg : forall x, 0 <= x < 288 -> ~ in_img B (r + x)).
  { intros x Hx. destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + x) HM MINE ltac:(lia))
      as (_ & N & _). exact N. }
  assert (Hspa : (spZ regs0 - 464) mod 16 = 0).
  { replace (spZ regs0 - 464) with (spZ regs0 + (-29) * 16) by lia. rewrite Z.mod_add by lia. exact Hal. }
  destruct (sg_list mem (Z.to_nat (inn - 1)) (ip + 1) ltac:(lia) ltac:(lia)) as (rest & Hrest & Hpay).
  { intros x Hx. apply (llvm_payload_read B API stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x CTX FR).
    lia. }
  change (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 8 j1 :: C8 (Z_to_bv 64 i) ::
          C8 (Z_to_bv 64 (bx_n bs)) :: CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 (ip + 1)) ::
          C8 (Z_to_bv 64 (inn - 1)) :: llvm_saved_cells regs0)
    with ([CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
           CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (inn - 1))] ++ llvm_saved_cells regs0) in FRC.
  destruct (top_rwc_split mem _ _ _ FRC) as [FRP FRS].
  assert (E360 : Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i);
                                         C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1));
                                         C8 (Z_to_bv 64 (inn - 1))]) = 360)
    by reflexivity.
  rewrite E360 in FRS.
  assert (FRPn : rw_cells rsegs (normalize rsegs mem) (spZ regs0 - 464)
    [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
     CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (inn - 1))]).
  { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro | | exact FRP].
    rewrite E360. intros x Hx Himg'. pose proof (lf_in_img_top B _ SEGS Himg'). lia. }
  assert (RWRn : rw_cells rsegs (normalize rsegs mem) r [CB 288 bs]).
  { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro | | exact RWR].
    change (Z.of_nat (cells_size [CB 288 bs])) with 288. exact Hrimg. }
  assert (STn : Frame.stk rsegs (normalize rsegs mem) (spZ regs0 - stk) (spZ regs0 - 464)).
  { apply lf_stk; [lia | lia |]. intros a Ha. unfold YP09.writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi'; pose proof (lf_in_img_top B a SEGS Hi'); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw a ltac:(lia)). }
  rewrite SEGS.
  eapply (llvm_run_norm fx' regs _ mem md); [exact Hh | exact Hl | exact Hro | | |].
  - apply (EV (@fp_regs fx') (@fp_csr fx') regs (normalize rsegs mem) (spZ regs0 - 464) (spZ regs0 - stk) r fab
             ip inn op i (p + n) (getr regs0 3) (getr regs0 4) j0 j1 jm bs rest);
      first [ assumption | exact (mem_inv_normalize rsegs mem) | exact (bytes_at_normalize rsegs mem _ _ Hro Hpay)
            | lia ].
  - intros ms HQ.
    destruct HQ as (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' &
      s6' & s7' & t3' & t4' & t5' & t6' & m'' & j0' & j1' & jm' & q & cc & bs' & -> & _).
    do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' &
      s6' & s7' & t3' & t4' & t5' & t6' & m'' & j0' & j1' & jm' & q & cc & bs' & HE & E3' & E6' & E7' & MU & WM & MI &
      FRC' & Hq & Hc & Hqe & HB' & WR' & INV' & Hfab' & KEPT).
    injection HE as ER EF EP EC EM. subst R F pc' fc m''.
    rewrite MState.unsigned_lit in MU, FRC' by lia.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU)
      as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM)
      as WM'.
    pose proof (ro_agree_same rsegs mem m' Hro Hsame) as Hro'.
    assert (AL' : llvm_alloc B API stk L0 A0 regs0 mem0 md0 b L A m' md r k).
    { apply (llvm_alloc_mem stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md r k m' _ CTX AL MU' WM' Hro').
      intros x Hx0 NO.
      destruct (Z_le_dec (spZ regs0 - stk) x); destruct (Z_lt_dec x (spZ regs0 - 464 + 360));
        destruct (Z_le_dec r x); destruct (Z_lt_dec x (r + 288)); try lia;
        exfalso; apply NO; cbn [outside]; repeat split; lia. }
    pose proof (rw_cells_transport rsegs _ mem m' _ _ FRS MU' WM') as FRS'.
    assert (FRS'' : rw_cells rsegs m' (spZ regs0 - 464 + 360) (llvm_saved_cells regs0)).
    { apply FRS'. unfold llvm_saved_cells. cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    pose proof (lf_rw_cells_rel m' m0' _ _ Hrel FRC') as FRC''.
    pose proof (top_rwc_join m' _ _ _ _ FRC'' ltac:(reflexivity) FRS'') as FRJ.
    pose proof (lf_rw_cells_rel m' m0' _ _ Hrel (sg_rw_mk m0' r bs' HB' (proj1 (proj1 INV')) WR')) as RWR'.
    apply SR_ret.
    exists k, (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A, r, fab, q, cc, bs, bs', (-1), j0', j1', jm'.
    split; [rewrite SEGS; reflexivity|].
    split; [exact Hfrm|].
    split.
    { unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact E6'|]. split; [exact E7'|].
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    split; [rewrite (lf_getr_eqv _ _ _ Hx); rewrite E3'; reflexivity|].
    split; [exact FRJ|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold boxreg_B1 in B1; lia|].
    split; [exact INV|]. split; [exact Hfab|].
    split; [exact RWR'|]. split; [exact INV'|]. split; [exact Hfab'|]. split; [exact KEPT|].
    split; [exact AL' | lia].
Qed.

End G.
