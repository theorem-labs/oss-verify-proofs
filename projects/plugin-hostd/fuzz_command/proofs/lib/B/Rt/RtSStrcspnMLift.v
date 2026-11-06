(* The lift between the two models this walk uses, for the musl half of strcspn: a walk proved over the machine
   state alone (lib/Lib `evt`, registers written `mkR ...`, memory read through lib/Lib/Mem `mrd`) read at a call
   site of cgif's model (`SRr` from `cfg_at`, Reusable/YG0d.v:213, over the store `mem` restricted by the world's
   hidden set). The generic part is lib/B/Rt/RtBzLift.v (omx-clap-core/fuzz_manifest's FMrt_lift.v relocated:
   canon_at, srr_of_canon, ms_eqv_getr, unrestrict_ret, win_mem); this file adds what the strcspn walk needs beyond it:

   - `srr_of_canon_cont`: RtBzLift.srr_of_canon with the configuration the walk stops at left to a continuation,
     so the same lemma serves a walk that returns and a walk that stops at a call; `unrestrict_at` reads the
     configuration of a walk that stops at a literal program counter.
   - `art_post_comp` reads the post of a walk that returns to ra, keeps the callee-saved registers and changes
     nothing but WK <= STK bytes below sp, as RtDefs.art_post at window STK (RtBzLift.rt_post_ro_win states it for
     fm's rt_post_ro).  AR is kept by the frame law (al_frame, YG0d.v:447), whose premises come from win_mem and
     al_stack.  The walk may run on a store the run reached through an earlier call, which enters by two bridge
     premises.
   - the premise side, in the shape of omx-clap-core/fuzz_manifest's FMstrstr.v (:67-200): lib/Lib `bytes_at`, `wr_at`
     and `stk` out of the donor's `aview` / `apresent`, and the image bytes of a read-only word out of rt_rom_view. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK14 YK15 YK18 YP03 YP09 YK04 YK0i YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtSStrcspnMImg RtBzLift.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.PropExec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Regs6ss.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.PropExec.
Module LM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.
Module LF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Frame.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a walk from the call site, read in the donor's form, with the configuration it stops at left to [K] *)
Theorem srr_of_canon_cont : forall (W : world tfibsegs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
LE.evt rsegs Q (canon_at regs pc (mrestrict (w_H W) mem)) ->
(forall ms0 ms' model', Q ms0 -> R6.ms_eqv ms0 ms' -> same_but_materialized md model' ->
hclean (w_H W) ms' -> SRr tfibsegs W (mkCfg (unrestrict (w_H W) mem ms') model') POST) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
intros W pc regs mem md Q POST Hev HK.
apply (SRr_bind tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists ms0 ms' model', Q ms0 /\ R6.ms_eqv ms0 ms' /\ same_but_materialized md model' /\
hclean (w_H W) ms' /\ c' = mkCfg (unrestrict (w_H W) mem ms') model') POST).
- apply (srr_of_canon W pc regs mem md Q _ Hev).
intros ms0 ms' model' HQ Heqv Hsame Hcl. split; [reflexivity|].
exists ms0, ms', model'. split; [exact HQ|]. split; [exact Heqv|]. split; [exact Hsame|].
split; [exact Hcl | reflexivity].
- intros W' c' _ (-> & ms0 & ms' & model' & HQ & Heqv & Hsame & Hcl & ->).
exact (HK ms0 ms' model' HQ Heqv Hsame Hcl).
Qed.

(* the same at a walk that stops at a literal program counter (a call it cannot step through) *)
Lemma unrestrict_at : forall (pc : Z) (H : word -> bool) mem ms0 ms',
R6.ms_eqv ms0 ms' ->
ms_pc_val ms0 = w64 pc -> ms_fregs ms0 = fp_regs -> ms_svc_pending ms0 = None ->
ms_resv ms0 = None -> ms_fcsr ms0 = fp_csr -> ms_rom ms0 = seg_rom tfibsegs ->
unrestrict H mem ms' = mkst (ms_regs ms') (w64 pc) (munrestrict H mem (ms_mem ms')) (seg_rom tfibsegs).
Proof.
intros pc H mem ms0 ms' (_ & Ef & Ep & Es & Er & Ec & _ & Ero) P0 F0 S0 R0 C0 RO0.
unfold unrestrict, mkst.
rewrite <- Ef, <- Ep, <- Es, <- Er, <- Ec, <- Ero, F0, P0, S0, R0, C0, RO0. reflexivity.
Qed.

Lemma nth_err_nth : forall (l : list byte) (d : byte) i, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof.
induction l as [|x l IH]; intros d [|i] H; cbn in H |- *; try lia; [reflexivity | apply IH; lia].
Qed.

Section p.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The post of a walk that returns to ra, keeps the callee-saved registers and changes nothing but WK <= STK
   bytes below sp, read as art_post at the window STK.  The walk may start from a store [base] the run reached
   through earlier calls, so [base] enters by the two bridge premises (the donor's view outside the window, and
   presence); with base := mem they are reflexivity. *)
Theorem art_post_comp : forall (STK WK : Z) ly S (W : world tfibsegs) regs (mem base : word -> option byte)
md mdb (E : Z -> Prop) (Q : bvmap 5 word -> (word -> option byte) -> Prop) ms0 ms' model',
ecall_pre_stk tfibsegs B STK ly S W regs mem md -> 0 <= WK <= STK ->
AR tfibsegs B ly S W base mdb ->
same_but_materialized md mdb -> same_but_materialized mdb model' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) ->
 aview tfibsegs (w_H W) base a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) base a) ->
R6.ms_eqv ms0 ms' ->
ms_pc_val ms0 = LMS.ret_pc (getr regs 1) -> ms_fregs ms0 = fp_regs -> ms_svc_pending ms0 = None ->
ms_resv ms0 = None -> ms_fcsr ms0 = fp_csr -> ms_rom ms0 = seg_rom tfibsegs ->
(forall r, acallee_saved r -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall xw : word, ~ (spZ regs - WK <= bv_unsigned xw < spZ regs) -> ms_mem ms0 xw = mrestrict (w_H W) base xw) ->
(forall a, spZ regs - WK <= a < spZ regs -> ms_mem ms0 (Z_to_bv 64 a) <> None) ->
Q (ms_regs ms') (munrestrict (w_H W) base (ms_mem ms')) ->
art_post tfibsegs B STK ly S W regs mem md E Q W (mkCfg (unrestrict (w_H W) base ms') model').
Proof.
intros STK WK ly S W regs mem base md mdb E Q ms0 ms' model' HPRE HK HARb Hsb1 Hsb2 AVb PRb Heqv
P0 F0 S0 R0 C0 RO0 KEEP MOUT MIN HQ.
destruct HPRE as (HEP & Hslo & HpresS).
pose proof HEP as (HAR & Hra & _ & _ & Hshi & _ & _ & _).
pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _). rewrite Emem in MOUT, MIN.
destruct (win_mem (w_H W) base (ms_mem ms') (spZ regs - WK) (spZ regs) MOUT MIN
ltac:(intros a Ha; apply PRb; apply HpresS; unfold ascratch_stk; lia)) as (AV & VIS & HB & PRS).
destruct (same_but_materialized_frame mdb model' Hsb2)
as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
assert (HAR' : AR tfibsegs B ly S W (munrestrict (w_H W) base (ms_mem ms')) model').
{ apply (al_frame _ _ LAWS ly S W base mdb _ model' HARb); [| exact VIS | exact E1 | exact E2 | exact E3 |].
- intros a Hr Hown. apply AV; [exact Hr|]. intros Hw.
exact (al_stack _ _ LAWS ly S W base mdb a HARb ltac:(lia) Hown).
- intros a _ Hh. exact (HB a Hh). }
unfold art_post. split; [reflexivity|].
exists (ms_regs ms'), (munrestrict (w_H W) base (ms_mem ms')), model'.
split; [unfold cfg_at; f_equal; exact (unrestrict_ret regs (w_H W) base ms0 ms' Heqv Hra P0 F0 S0 R0 C0 RO0)|].
split; [exact HAR'|].
split; [intros r Hr; rewrite (ms_eqv_getr ms0 ms' _ Heqv); exact (KEEP r Hr)|].
split; [exact (same_but_materialized_trans _ _ _ Hsb1 Hsb2)|].
split; [exact HQ|].
split; [intros a Ha Hn _; rewrite (AV a Ha ltac:(unfold ascratch_stk in Hn; lia)); apply AVb; [exact Ha | exact Hn]|].
split; [intros a Hp; apply PRS; apply PRb; exact Hp|].
intros a Ha. apply PRS. apply PRb. apply HpresS. exact Ha.
Qed.

End p.

(* ---- bytes: the donor's reader and lib/Lib's ---- *)

Lemma view_mrd : forall (H : word -> bool) mem a v,
aview tfibsegs H mem a = Some v ->
exists b, LM.mrd rsegs (mrestrict H mem) (LM.wa a) = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v Ev. unfold aview in Ev.
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Eb; [|discriminate].
cbn in Ev. injection Ev as <-. exists b. split; [exact Eb | reflexivity].
Qed.

Lemma view_some_mrd : forall (H : word -> bool) mem a, aview tfibsegs H mem a <> None ->
exists b, LM.mrd rsegs (mrestrict H mem) (LM.wa a) = Some b.
Proof.
intros H mem a Ev. destruct (aview tfibsegs H mem a) as [v|] eqn:E; [|exfalso; exact (Ev eq_refl)].
destruct (view_mrd H mem a v E) as (b & Eb & _). exists b. exact Eb.
Qed.

(* the bytes of a list the donor's reader sees, as lib/Lib bytes *)
Lemma bytes_of_view : forall (H : word -> bool) (mem : word -> option byte) a (l : list byte),
0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
(forall i, (i < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0)))) ->
LM.bytes_at rsegs (mrestrict H mem) a l.
Proof.
intros H mem a l Ha Hl HK. split; [exact Ha|]. split; [exact Hl|].
intros i Hi. destruct (view_mrd H mem _ _ (HK i Hi)) as (b & Eb & Ub). rewrite Eb.
rewrite (nth_err_nth l (Z_to_bv 8 0) i Hi). f_equal. apply bv_eq. exact Ub.
Qed.

(* every byte of a list a reader exhibits at all, when only presence matters *)
Lemma bytes_exist_view : forall (H : word -> bool) (mem : word -> option byte) a (k : nat),
0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
(forall i, (i < k)%nat -> aview tfibsegs H mem (a + Z.of_nat i) <> None) ->
exists bs, length bs = k /\ LM.bytes_at rsegs (mrestrict H mem) a bs.
Proof.
intros H mem a k Ha Hk HV.
assert (HB : forall i, (i < k)%nat -> exists b, LM.mrd rsegs (mrestrict H mem) (LM.wa (a + Z.of_nat i)) = Some b)
by (intros i Hi; apply view_some_mrd; exact (HV i Hi)).
clear HV. revert Hk HB. induction k as [|k IH]; intros Hk HB.
- exists []. split; [reflexivity|]. split; [exact Ha|]. cbn [length]. split; [lia|]. intros i Hi. lia.
- destruct (IH ltac:(lia) ltac:(intros i Hi; apply HB; lia)) as (bs & Lbs & Bbs).
  destruct (HB k ltac:(lia)) as (b & Hb).
  exists (bs ++ [b]). rewrite length_app, Lbs. cbn [length]. split; [lia|].
  destruct Bbs as (_ & _ & Bb). split; [exact Ha|]. rewrite length_app, Lbs. cbn [length]. split; [lia|].
  intros i Hi.
  destruct (Nat.eq_dec i k) as [->|NE].
  + rewrite nth_error_app2 by lia. rewrite Lbs, Nat.sub_diag. cbn [nth_error]. exact Hb.
  + rewrite nth_error_app1 by lia. apply Bb. lia.
Qed.

(* the stack window the donor's ecall_pre gives, as lib/Lib's stk *)
Lemma stk_of_apresent : forall (H : word -> bool) mem lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
(forall a, lo <= a < hi -> apresent H mem a) -> LF.stk rsegs (mrestrict H mem) lo hi.
Proof.
intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
assert (Em : mrestrict H mem (LM.wa a) = Some b) by (unfold mrestrict, LM.wa; rewrite HH; exact Hb).
split.
- unfold wview. rewrite Em. discriminate.
- exists b. unfold LM.mrd. rewrite Em. reflexivity.
Qed.

Lemma wr_at_of_apresent : forall (H : word -> bool) mem A n, 0 <= A -> A + n <= 2 ^ 64 ->
(forall a, A <= a < A + n -> apresent H mem a) -> LM.wr_at rsegs (mrestrict H mem) A n.
Proof.
intros H mem A n HA Hn HP. split; [exact HA|]. split; [exact Hn|].
intros i Hi. destruct (HP (A + i) ltac:(lia)) as (HH & b & Hb).
assert (Em : mrestrict H mem (LM.wa (A + i)) = Some b) by (unfold mrestrict, LM.wa; rewrite HH; exact Hb).
unfold wview. rewrite Em. discriminate.
Qed.

Lemma writable_of_apresent : forall (H : word -> bool) mem a,
apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a (HH & b & Hb). unfold writable_at, wview, mrestrict. rewrite HH, Hb. discriminate.
Qed.

(* ---- the stack is above the image, so a byte the walk leaves there is in the store ---- *)
Lemma seg_rom_none_high_L : forall a, 0x606000 <= a < 2 ^ 64 -> LP.seg_rom rsegs (Z_to_bv 64 a) = None.
Proof. intros a Ha. exact (YF0x.seg_rom_none_high a Ha). Qed.

Lemma nz_of_stk : forall (m : word -> option byte) lo hi a, LF.stk rsegs m lo hi ->
lo <= a < hi -> 0x606000 <= a < 2 ^ 64 -> m (Z_to_bv 64 a) <> None.
Proof.
intros m lo hi a (_ & _ & HS) Ha Hi. destruct (HS a Ha) as (_ & b & Hb).
unfold LM.mrd, LM.wa in Hb. rewrite (seg_rom_none_high_L a Hi) in Hb.
intros Hn. rewrite Hn in Hb. discriminate.
Qed.

Lemma nz_of_bytes : forall (m : word -> option byte) A bs a, LM.bytes_at rsegs m A bs ->
A <= a < A + Z.of_nat (length bs) -> 0x606000 <= a < 2 ^ 64 -> m (Z_to_bv 64 a) <> None.
Proof.
intros m A bs a (_ & _ & HB) Ha Hi.
assert (Hk : (Z.to_nat (a - A) < length bs)%nat) by lia.
pose proof (HB (Z.to_nat (a - A)) Hk) as Hr.
replace (A + Z.of_nat (Z.to_nat (a - A))) with a in Hr by lia.
destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
unfold LM.mrd, LM.wa in Hr. rewrite (seg_rom_none_high_L a Hi) in Hr.
intros Hn. rewrite Hn in Hr. discriminate.
Qed.

Lemma nz_of_cells : forall (m : word -> option byte) A cs a, LSt.rw_cells rsegs m A cs ->
A <= a < A + Z.of_nat (LC.cells_size cs) -> 0x606000 <= a < 2 ^ 64 -> m (Z_to_bv 64 a) <> None.
Proof.
intros m A cs a ((Hwf & HB) & _) Ha Hi.
rewrite <- (LC.cells_bytes_length cs Hwf) in Ha. exact (nz_of_bytes m A _ a HB Ha Hi).
Qed.

(* ---- a read-only word of the image, out of rt_rom_view ---- *)
Lemma rom_bytes_at : forall (W : world tfibsegs) mem a (bs : list byte),
0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
(forall i, (i < length bs)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i) ->
(forall i, (i < length bs)%nat ->
 aview tfibsegs (w_H W) mem (a + Z.of_nat i) =
 option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i)))) ->
LM.bytes_at rsegs (mrestrict (w_H W) mem) a bs.
Proof.
intros W mem a bs Ha Hl HR HV. apply bytes_of_view; [exact Ha | exact Hl |].
intros i Hi. rewrite (HV i Hi), (HR i Hi).
rewrite (nth_err_nth bs (Z_to_bv 8 0) i Hi). reflexivity.
Qed.

End l.
