(** Helper lemmas and tactics for the check_csv walk of the plain image (Prog/check_csv.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/disco_table.v:112 *)
Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/disco_table.v:116 *)
Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_ctrl/lib/Prog/Seg/G03.v:24 (g03_memcmp) *)
Lemma ccsv_memcmp : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|x l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(** A byte store of a literal: the store writes [le1 (Z_to_bv 64 z)], one byte cell. *)
Lemma le1_lit : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. rewrite <- (le1_zxb (Z_to_bv 8 z)). f_equal. unfold zxb. f_equal.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma land1 : forall v, Z.land v 1 = v mod 2.
Proof. intros v. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma swrap_par : forall y, bv_unsigned (Z_to_bv 64 (bv_swrap 32 y)) mod 2 = y mod 2.
Proof. intros y. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

(** The bit test `srlw t4, a3, a0; andi t4, t4, 1; beqz t4` with a0 = i < 32. *)
Lemma ccsv_bit : forall X i, 0 <= X -> 0 <= i < 32 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 X) (i mod 32))))) 1))
         (Z_to_bv 64 0) = negb (Z.testbit X i).
Proof.
  intros X i HX Hi. rewrite (Z.mod_small i 32) by lia. rewrite land1, swrap_par.
  rewrite Z.shiftr_div_pow2 by lia. rewrite <- Z.testbit_spec' by lia.
  replace (Z.testbit (bv_wrap 32 X) i) with (Z.testbit X i).
  - destruct (Z.testbit X i); reflexivity.
  - unfold bv_wrap, bv_modulus. cbn [Z.of_N]. symmetry. apply Z.mod_pow2_bits_low. lia.
Qed.

(** Two addresses a little apart from one base are different words. *)
Lemma eqb_off : forall x a b, a <> b -> - 2^64 < a - b < 2^64 ->
  bv_eqb (Z_to_bv 64 (x + a)) (Z_to_bv 64 (x + b)) = false.
Proof.
  intros x a b N H. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq. intros E.
  pose proof (Z.div_mod (x + a) (2^64) ltac:(lia)) as D1. pose proof (Z.div_mod (x + b) (2^64) ltac:(lia)) as D2.
  assert (Q : (x + a) / 2^64 = (x + b) / 2^64 \/ (x + a) / 2^64 <> (x + b) / 2^64) by lia.
  destruct Q as [Q|Q]; nia.
Qed.

(** Group the first k cells after [pre] into one byte cell. *)
Lemma rw_cells_group_at : forall segs m A pre cs k,
  rw_cells segs m A (pre ++ cs) ->
  rw_cells segs m A (pre ++ CB (cells_size (firstn k cs)) (cells_bytes (firstn k cs)) :: skipn k cs).
Proof.
  intros segs m A pre cs k H. rewrite <- (firstn_skipn k cs) in H. apply rw_cells_merge. exact H.
Qed.

Lemma rw_cells_want : forall m A d W W' rest,
  rw_cells rsegs m A (CB 8 d :: CB 40 W :: rest) -> W = W' -> rw_cells rsegs m A (CB 8 d :: CB 40 W' :: rest).
Proof. intros; subst; assumption. Qed.

Lemma bytes_at_firstn : forall m A l k, bytes_at rsegs m A l -> bytes_at rsegs m A (firstn k l).
Proof. intros m A l k H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma firstn_app_len : forall {X} (l1 l2 : list X) n, length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof. intros X l1 l2 n <-. apply firstn_app_exact. Qed.

(** A step whose store writes a literal byte: turn [le1 (Z_to_bv 64 z)] into a byte cell, then do what
    [mem_after_store_opt] does. *)
Ltac ccsv_fix_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      is_Zlit z; rewrite (le1_lit z) by lia; mem_after_store_opt
  | _ => idtac
  end.

Ltac cstep := step; ccsv_fix_store.

(** A branch: literal conditions, or two addresses off one base. *)
Ltac cbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ if_false | if_true
            | rewrite eqb_off by lia; cbn [negb]; cbv iota ]
  | _ => idtac
  end.

Ltac run_to pc :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => cstep; cbr
  end.

(** The frame and the states of the walk. Frame (96 bytes at sp): d[8] at sp, want[40] at sp + 8, then the saved
    s4, s3, s2, s1, s0, ra (sp + 0x30 .. sp + 0x5f). *)
Definition ccsv_SV (ra s0 s1 e2 e3 e4 : word) : list cell := [C8 e4; C8 e3; C8 e2; C8 s1; C8 s0; C8 ra].

(** The state inside the outer loop: i in a0, n (the length of want) in a7, sp = Sp - 96; s2-s4 and t4-t6 hold
    scratch values. *)
Definition ccsv_CS (ra gp tp bufw lenw a1 a3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Sp pc i n : Z) (y18 y19 y20 y29 y30 y31 : word) (m : word -> option byte) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (Sp + -96)) gp tp (Z_to_bv 64 (Sp + -88)) (Z_to_bv 64 67144) (Z_to_bv 64 1717986919)
          bufw lenw (Z_to_bv 64 i) a1 (Z_to_bv 64 (Sp + -97)) a3 (Z_to_bv 64 3) (Z_to_bv 64 10) (Z_to_bv 64 18)
          (Z_to_bv 64 n) y18 y19 y20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 44) y29 y30 y31)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(** check_csv_contract's postcondition, with S = Sp and the caller's s2, s3, s4 = e2, e3, e4. *)
Definition ccsv_post (ra gp tp s0 s1 e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Sp lo : Z) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp + -96, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp.

(** At 0x14818: regroup the frame cells (the 6 cells of d, then the [kc] cells of want) and continue with K. *)
Ltac ccsv_join K kc :=
  lazymatch goal with
  | H : rw_cells rsegs _ _ (C1 _ :: _) |- _ =>
      apply (rw_cells_group_at _ _ _ [] _ 6) in H;
      cbn [app firstn skipn cells_size csize cells_bytes cbytes Nat.add] in H;
      lazymatch type of H with rw_cells _ _ _ (?c :: _) => apply (rw_cells_group_at _ _ _ [c] _ kc) in H end;
      cbn [app firstn skipn cells_size csize cells_bytes cbytes Nat.add] in H;
      eapply K; [ eapply rw_cells_want; [exact H | ] | assumption .. ]
  end.
