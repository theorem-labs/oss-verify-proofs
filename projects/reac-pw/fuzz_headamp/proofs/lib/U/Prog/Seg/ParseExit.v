(** The exit of the walk of reac_headamp_prop_parse_result (UBSan image): the cuts [S_EPI] and [S_EXIT] of
    U/Prog/Seg/ParseCut.v (the plain file lib/Prog/Seg/ParseExit.v with the UBSan code's frame and registers).
      - [px_epi]: from 0x15108, a0 = s1, the thirteen reloads of ra, s0 .. s11, fs0 (any value: the post's F' is
        free), sp back by 0x90, ret; the frame goes back to the stack below the caller's sp (fuzz_role's [epi]).
      - [px_exit]: from 0x15150, res = 0 goes straight to 0x15108; else the res & 3 trap at 0x15158 is not taken
        (res mod 4 = 0), res->n = s1, res->keys = s5, res->refusal = the frame's 0x08 (0x1515c-0x15168,
        reac_headamp_prop.c:176-179) into the 12 writable bytes at res, then [S_EPI] with the folded answer; the
        frame's temporary cells are merged into one block of 40 bytes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Step FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import ParseCut.
Import ListNotations.
Open Scope Z_scope.

(** ** The call's facts the exit reads *)
Lemma px_facts : forall c, pc_ok c ->
  0 <= c_lo c /\ c_lo c + PARSE_STACK <= bv_unsigned (c_sp c) /\ bv_unsigned (c_sp c) < 2^64 /\ 0 <= c_cap c /\
  (c_R c <> 0 -> wr_at rsegs (c_m c) (c_R c) 12 /\ c_R c mod 4 = 0 /\ bv_unsigned (c_sp c) <= c_R c /\
                 disjoint_from [(c_E c, c_E c + 4)] (c_R c) 12) /\
  c_O c + 3 * (c_cap c + 1) <= c_lo c.
Proof.
  intros c (HA & HSTK & HLO & _ & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & HCAP & _ & _ & HOL & _ & HRR & _ & _ & HRD & _).
  pose proof HSTK as (L0 & _ & _).
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  split; [exact L0|]. split; [exact HLO|]. split; [lia|]. split; [lia|]. split; [|exact HOL].
  intros HR0. destruct HRR as [E|(W & H4 & HS)]; [contradiction|].
  destruct HRD as [E|HD]; [contradiction|]. split; [exact W|]. split; [exact H4|]. split; [exact HS|]. exact HD.
Qed.

(** The answer's cells are at most cap (Pod/Headamp.v's parse_model_total). *)
Lemma px_cells_cap : forall c cl keys rf, pc_ok c -> ha_result (cl, keys, rf) = RESM c ->
  Z.of_nat (length cl) <= c_cap c.
Proof.
  intros c cl keys rf HC HRES.
  pose proof (px_facts c HC) as (_ & _ & _ & HCAP & _).
  pose proof (parse_model_total (c_bs c) (c_cap c) HCAP) as HOK.
  unfold RESM in HRES. rewrite <- HRES in HOK.
  cbn [answer_ok ha_result] in HOK.
  destruct HOK as [[(E & _) | (E1 & E2 & _)] _]; lia.
Qed.

(** res's 12 bytes, writable in any memory of a cut. *)
Lemma px_wr : forall c fr cl m, pc_ok c -> c_R c <> 0 -> PMem c fr cl m -> wr_at rsegs m (c_R c) 12.
Proof.
  intros c fr cl m HC HR0 (_ & _ & _ & _ & _ & WM & _).
  pose proof (px_facts c HC) as (_ & _ & _ & _ & HRF & _).
  destruct (HRF HR0) as (W & _ & _).
  exact (wr_at_transport rsegs (c_m c) m (c_R c) 12 W WM).
Qed.

(** A store of 4 bytes inside res, with any frame of 0x90 bytes: the cut's memory is kept, the stored bytes are
    there. *)
Lemma px_st : forall c fr cl m (a : Z) (v : word),
  pc_ok c -> c_R c <> 0 -> c_R c <= a -> a + 4 <= c_R c + 12 -> Z.of_nat (length cl) <= c_cap c ->
  Z.of_nat (cells_size fr) = 144 ->
  PMem c fr cl m ->
  PMem c fr cl (write_to_mem m (Z_to_bv 64 a) (le4 v)) /\
  bytes_at rsegs (write_to_mem m (Z_to_bv 64 a) (le4 v)) a (le4 v).
Proof.
  intros c fr cl m a v HC HR0 Ha1 Ha2 HCL HFS HPM.
  pose proof (px_wr c _ cl m HC HR0 HPM) as WRm.
  destruct HPM as (FR & ST & MU & BO & (ev' & EV) & WM & MI).
  pose proof (px_facts c HC) as (HLO0 & HLO & HSP & HCAP & HRF & HOL).
  destruct (HRF HR0) as (WR & _ & HSR & HRD).
  pose proof WR as (HR0' & HR12 & _).
  unfold PARSE_STACK in HLO. cbn [disjoint_from] in HRD.
  change (Z_to_bv 64 a) with (wa a).
  split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
  - apply rw_cells_frame; [exact FR | lia | rewrite length_le4; lia |].
    left. rewrite HFS. unfold c_spf. lia.
  - apply stk_write; [exact ST | lia | rewrite length_le4; lia].
  - apply munch_write; [exact MU | lia | rewrite length_le4; lia |].
    unfold parse_writes. rewrite (proj2 (Z.eqb_neq _ _) HR0). cbn [app inside].
    rewrite length_le4. right; right; right; left. lia.
  - apply bytes_at_write_other; [exact BO | lia | rewrite length_le4; lia |].
    left. rewrite length_ha_cells_bytes. lia.
  - exists ev'. apply rw_cells_frame; [exact EV | lia | rewrite length_le4; lia |].
    cbn [cells_size csize]. rewrite length_le4. lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI|]. rewrite length_le4.
    replace (wa a) with (wa (c_R c + (a - c_R c))) by (f_equal; lia).
    apply (wr_at_store_ok rsegs m (c_R c) 12 (a - c_R c) 4 WRm); lia.
  - apply bytes_at_write_same; [lia | rewrite length_le4; lia].
Qed.

(** Bytes apart from a 4-byte store are kept. *)
Lemma px_keep : forall m (a : Z) (v : word) X bs, bytes_at rsegs m X bs -> 0 <= a -> a + 4 <= 2^64 ->
  X + Z.of_nat (length bs) <= a \/ a + 4 <= X -> bytes_at rsegs (write_to_mem m (Z_to_bv 64 a) (le4 v)) X bs.
Proof.
  intros m a v X bs B H0 H4 HD. change (Z_to_bv 64 a) with (wa a).
  apply bytes_at_write_other; [exact B | exact H0 | rewrite length_le4; lia | rewrite length_le4; lia].
Qed.

(** The walk's frame as [S_EPI]'s: its temporary cells merged into one block of 40 bytes. *)
Lemma px_merge : forall c rf ja jb cl m, PMem c (wframe c rf ja jb) cl m ->
  PMem c (CB 40 (cells_bytes [CB 8 ja; C8 (Z_to_bv 64 rf); CB 24 jb]) :: saves c) cl m.
Proof.
  intros c rf ja jb cl m (FR & HR). split; [|exact HR].
  exact (rw_cells_merge rsegs m (c_spf c) [] [CB 8 ja; C8 (Z_to_bv 64 rf); CB 24 jb] (saves c) FR).
Qed.

Lemma px_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** Branch tests: the condition of the pc's [if], decided on Z (fuzz_role's ua_go). *)
Ltac px_lia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac px_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; px_lia | apply Z.ltb_ge; px_lia
        | apply Z.leb_le; px_lia | apply Z.leb_gt; px_lia
        | apply Z.eqb_eq; px_lia | apply Z.eqb_neq; px_lia ].
Ltac px_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); px_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); px_cond_rec
  | _ => px_cond_base
  end.
Ltac px_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; zsimp; rewrite ?px_land3; px_cond_rec.
Ltac px_go b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; px_cond]
  end.

(** The memory of the goal's state, restated as M (convertible). *)
Ltac px_mem M :=
  lazymatch goal with
  | |- evt ?s ?Q (MS ?R ?F ?pc ?fc ?rv _ ?ro) => change (evt s Q (MS R F pc fc rv M ro))
  end.

(** ** [S_EPI]: the epilogue from 0x15108 *)
Lemma px_epi : forall c, pc_ok c -> S_EPI c.
Proof.
  intros c HC. unfold S_EPI.
  intros o m F fc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 ja (FR & ST & MU & BO & (ev' & EV) & WM & MI) HR HFRM.
  pose proof (px_facts c HC) as (HLO0 & HLO & HSP & _).
  unfold PARSE_STACK in HLO.
  unfold c_spf, saves in *. unfold c_E in MU, EV.
  unfold PPost.
  zstep. (* 0x15108 mv a0,s1 *)
  zstep. (* ld ra,0x88(sp) *)
  zstep. (* ld s0,0x80(sp) *)
  zstep. (* ld s1,0x78(sp) *)
  zstep. (* ld s2,0x70(sp) *)
  zstep. (* ld s3,0x68(sp) *)
  zstep. (* ld s4,0x60(sp) *)
  zstep. (* ld s5,0x58(sp) *)
  zstep. (* ld s6,0x50(sp) *)
  zstep. (* ld s7,0x48(sp) *)
  zstep. (* ld s8,0x40(sp) *)
  zstep. (* ld s9,0x38(sp) *)
  zstep. (* ld s10,0x30(sp) *)
  zstep. (* ld s11,0x28(sp) *)
  zstep. (* fld fs0,0x20(sp) *)
  zstep. (* addi sp,sp,0x90 *)
  release_frame FR ST (bv_unsigned (c_sp c)).
  zstep. (* ret *)
  finish.
  exact EV.
Qed.

(** ** [S_EXIT]: res's three words from 0x15150, then [S_EPI] *)
Lemma px_exit : forall c, pc_ok c -> S_EPI c -> S_EXIT c.
Proof.
  intros c HC HEPI. unfold S_EXIT.
  intros cl keys rf m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 ja jb HRES HPM HFRM.
  pose proof (px_cells_cap c cl keys rf HC HRES) as HCL.
  pose proof (px_facts c HC) as (HLO0 & HLO & HSP & HCAP & HRF & HOL).
  unfold PARSE_STACK in HLO.
  assert (HFS : Z.of_nat (cells_size (wframe c rf ja jb)) = 144) by (unfold wframe, saves; reflexivity).
  assert (HSPF : 0 <= c_spf c /\ c_spf c + 144 <= 2^64) by (unfold c_spf; lia).
  rewrite <- HRES.
  destruct (Z.eq_dec (c_R c) 0) as [R0|R0].
  - zstep. (* 0x15150 beqz s0 *)
    px_go true.
    eapply (HEPI (ha_result (cl, keys, rf))); [exact (px_merge c rf ja jb cl m HPM) | intros N; contradiction
                                                | exact HFRM].
  - destruct (HRF R0) as (WR & HR4 & HSR & _). pose proof WR as (HR0 & HR12 & _).
    zstep. (* 0x15150 beqz s0 *)
    px_go false.
    zstep. (* 0x15154 andi a0,s0,3 *)
    zstep. (* 0x15158 bnez a0: the trap, not taken (res mod 4 = 0) *)
    px_go false.
    pose proof (px_wr c _ cl m HC R0 HPM) as WR0.
    pose proof (wr_at_store_ok rsegs m (c_R c) 12 0 4 WR0 ltac:(lia) ltac:(lia)) as HS. rewrite Z.add_0_r in HS.
    zstep. (* 0x1515c sw s1,0(s0) *)
    px_mem (write_to_mem m (Z_to_bv 64 (c_R c)) (le4 (Z_to_bv 64 (Z.of_nat (length cl))))).
    destruct (px_st c _ cl m (c_R c) (Z_to_bv 64 (Z.of_nat (length cl))) HC R0 ltac:(lia) ltac:(lia) HCL HFS HPM)
      as (PM1 & B1).
    clear HS WR0. set (m1 := write_to_mem m (Z_to_bv 64 (c_R c)) (le4 (Z_to_bv 64 (Z.of_nat (length cl))))) in *.
    clearbody m1. clear HPM.
    pose proof (px_wr c _ cl m1 HC R0 PM1) as WR1.
    pose proof (wr_at_store_ok rsegs m1 (c_R c) 12 4 4 WR1 ltac:(lia) ltac:(lia)) as HS.
    zstep. (* 0x15160 sw s5,4(s0) *)
    px_mem (write_to_mem m1 (Z_to_bv 64 (c_R c + 4)) (le4 (Z_to_bv 64 keys))).
    destruct (px_st c _ cl m1 (c_R c + 4) (Z_to_bv 64 keys) HC R0 ltac:(lia) ltac:(lia) HCL HFS PM1) as (PM2 & B2).
    pose proof (px_keep m1 (c_R c + 4) (Z_to_bv 64 keys) (c_R c) _ B1 ltac:(lia) ltac:(lia)
                  ltac:(rewrite length_le4; lia)) as B1'.
    clear HS WR1. set (m2 := write_to_mem m1 (Z_to_bv 64 (c_R c + 4)) (le4 (Z_to_bv 64 keys))) in *.
    clearbody m2. clear PM1 B1.
    pose proof PM2 as (FR2 & _). unfold wframe in FR2.
    zstep. (* 0x15164 ld a0,8(sp): rf *)
    clear FR2.
    pose proof (px_wr c _ cl m2 HC R0 PM2) as WR2.
    pose proof (wr_at_store_ok rsegs m2 (c_R c) 12 8 4 WR2 ltac:(lia) ltac:(lia)) as HS.
    zstep. (* 0x15168 sw a0,8(s0) *)
    px_mem (write_to_mem m2 (Z_to_bv 64 (c_R c + 8)) (le4 (Z_to_bv 64 rf))).
    destruct (px_st c _ cl m2 (c_R c + 8) (Z_to_bv 64 rf) HC R0 ltac:(lia) ltac:(lia) HCL HFS PM2) as (PM3 & B3).
    pose proof (px_keep m2 (c_R c + 8) (Z_to_bv 64 rf) (c_R c) _ B1' ltac:(lia) ltac:(lia)
                  ltac:(rewrite length_le4; lia)) as B1''.
    pose proof (px_keep m2 (c_R c + 8) (Z_to_bv 64 rf) (c_R c + 4) _ B2 ltac:(lia) ltac:(lia)
                  ltac:(rewrite length_le4; lia)) as B2'.
    clear HS WR2. set (m3 := write_to_mem m2 (Z_to_bv 64 (c_R c + 8)) (le4 (Z_to_bv 64 rf))) in *.
    clearbody m3. clear PM2 B1' B2.
    zstep. (* 0x1516c j 0x15108 *)
    eapply (HEPI (ha_result (cl, keys, rf))); [exact (px_merge c rf ja jb cl m3 PM3) | intros _ | exact HFRM].
    cbn [ans_res_bytes ans_n ans_keys ans_rf ha_result fst snd]. unfold ha_res_bytes.
    apply (proj2 (bytes_at_app rsegs m3 _ _ _)). split; [exact B1''|].
    rewrite length_le4. replace (c_R c + Z.of_nat 4) with (c_R c + 4) by lia.
    apply (proj2 (bytes_at_app rsegs m3 _ _ _)). split; [exact B2'|].
    rewrite length_le4. replace (c_R c + 4 + Z.of_nat 4) with (c_R c + 8) by lia.
    exact B3.
Qed.
