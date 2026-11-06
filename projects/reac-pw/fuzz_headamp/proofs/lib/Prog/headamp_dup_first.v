(** first = fuzz_dup(out, 3 max(rc, 0)) in LLVMFuzzerTestOneInput (plain), past its malloc: the walk of
    [0x14168, 0x14184) against headamp_dup_first_contract (Prog/LLVMFuzzerTestOneInput_c.v), from memcpy's contract
    (Prog/memcpy_c.v).

    0x14168 `beqz a0` falls through (first <> 0, and first is below 2^64 by its writable cells); 0x1416c `mv s7,a0`;
    0x14170 `blez s6` on rc (a 32-bit value sign-extended in s6): for rc <= 0 it jumps to 0x14184 with nothing
    written; for rc > 0, 0x14174-0x1417c a0 = first, a1 = out, a2 = s8 = 3 rc and `jal memcpy` at 0x14180 (memcpy at
    0x1d248, ra = 0x14184): the source is out's 3 rc bytes w, the destination first's first_req rc = 3 rc writable
    bytes, the two apart. The evt ends at 0x14184, before the memset of the plain parse. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import memcpy_c SlotInv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Lemma df_eqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma df_rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(** `blez s6` with s6 = rc, a 32-bit int: the signed test 0 < s6 is 0 < rc. *)
Lemma df_lts0 : forall rc, - 2 ^ 31 <= rc < 2 ^ 31 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 rc) = (0 <? rc).
Proof.
  intros rc H. rewrite bv_lts_zero_l, unsigned_lit_wrap. destruct (Z.ltb_spec 0 rc) as [Hp | Hn].
  - rewrite Z.mod_small by lia. apply andb_true_iff. split; apply Z.ltb_lt; lia.
  - destruct (Z.eq_dec rc 0) as [-> | Hz]; [reflexivity|].
    replace (rc mod 2 ^ 64) with (rc + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
    apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Theorem headamp_dup_first_holds : memcpy_c.memcpy_contract -> headamp_dup_first_contract.
Proof.
  intros MCPY. unfold headamp_dup_first_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w junk rc out first -> Hfirst -> -> Hrc -> HW HFC HSEP MI.
  assert (HQ : 1 <= first_req rc) by (unfold first_req; destruct (0 <? rc) eqn:E; [apply Z.ltb_lt in E; lia | lia]).
  pose proof (rw_cells_bound rsegs m first _ HFC) as HFB. cbn [cells_size csize] in HFB.
  rewrite ?Nat.add_0_r, Z2Nat.id in HFB by lia.
  unfold HEAD_DUP_FIRST, HEAD_PLAIN.
  (* 0x14168 beqz a0: first <> 0 *)
  step. rewrite df_eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x1416c mv s7,a0; 0x14170 blez s6 *)
  step. step. rewrite df_lts0 by lia.
  destruct (Z.ltb_spec 0 rc) as [Hpos | Hneg]; cbn [negb].
  - (* rc > 0: memcpy(first, out, 3 rc) *)
    destruct (HW Hpos) as [HWL HWB]. pose proof HWB as (HO0 & HO1 & _). rewrite HWL in HO1.
    assert (EQ : first_req rc = 3 * rc) by (unfold first_req; rewrite (proj2 (Z.ltb_lt 0 rc) Hpos); reflexivity).
    rewrite EQ in HFC, HSEP, HFB |- *. rewrite Z.max_l in HSEP |- * by lia.
    (* 0x14174 mv a0,s7; mv a1,s3; mv a2,s8; 0x14180 jal memcpy *)
    step. step. step. step.
    eapply evt_cut.
    { eapply MCPY with (src := w) (junk := junk); rewrite ?unsigned_lit by lia.
      - exact HWB.
      - lia.
      - exact HFC.
      - lia.
      - exact MI. }
    intros ms' Hpost. unfold memcpy_post in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                       E & MU1 & WM1 & MI1 & CB1 & _).
    subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    (* 0x14184: the evt's end *)
    apply evt_done. do 16 eexists. exists m1.
    split; [reflexivity|].
    split; [intros _; exact (df_rw_bytes _ _ _ _ CB1)|].
    split; [exact MU1|]. split; [exact WM1 | exact MI1].
  - (* rc <= 0: the jump to 0x14184, nothing written *)
    apply evt_done. do 16 eexists. exists m.
    split; [reflexivity|].
    split; [intros H; lia|].
    split; [apply munch_refl|]. split; [apply wmono_refl | exact MI].
Qed.
