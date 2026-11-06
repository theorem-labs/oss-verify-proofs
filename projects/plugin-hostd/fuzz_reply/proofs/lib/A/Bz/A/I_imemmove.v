(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_pcap/lib/A/Bz/A/I_imemmove.v
   (a working branch eabce720039), with its module paths changed and its three code addresses moved
   from fuzz_pcap.asan's __sanitizer_internal_memmove (0x63c18) to fuzz_reply.asan's (0x651ac): the 22 words are
   identical, so each pc keeps its offset (+0x0, +0x10, +0x38). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Definition imemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d n : Z) (xs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' d [CB (Z.to_nat n) xs].

Lemma mm_rd : forall (m : word -> option byte) p x rest,
  bytes_at asegs m p (x :: rest) -> ov_read_bytes asegs m (Z_to_bv 64 p) 1 = Some [x].
Proof.
  intros m p x rest H.
  pose proof (bytes_at_ov_read asegs m p (x :: rest) 0 1 H ltac:(cbn [length]; lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma mm_last : forall (m : word -> option byte) s x pre,
  bytes_at asegs m s (pre ++ [x]) -> ov_read_bytes asegs m (Z_to_bv 64 (s + Z.of_nat (length pre))) 1 = Some [x].
Proof.
  intros m s x pre B. apply bytes_at_app in B. destruct B as [_ B]. exact (mm_rd m _ x [] B).
Qed.

Lemma mm_st : forall (m : word -> option byte) d n q,
  wr_at asegs m d n -> d <= q -> q + 1 <= d + n -> store_ok asegs m (Z_to_bv 64 q) 1 = true.
Proof.
  intros m d n q W H1 H2.
  pose proof (wr_at_store_ok asegs m d n (q - d) 1 W ltac:(lia) ltac:(change (Z.of_nat 1) with 1; lia)) as S.
  replace (d + (q - d)) with q in S by lia. exact S.
Qed.

Lemma mm_wr_of_rw : forall (m : word -> option byte) d n junk, 0 <= n ->
  rw_cells asegs m d [CB (Z.to_nat n) junk] -> wr_at asegs m d n.
Proof.
  intros m d n junk N H. destruct H as [_ W]. cbn [cells_size csize] in W.
  rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W.
Qed.

Lemma mm_rw_intro : forall (m : word -> option byte) d n xs, 0 <= n -> length xs = Z.to_nat n ->
  bytes_at asegs m d xs -> wr_at asegs m d n -> rw_cells asegs m d [CB (Z.to_nat n) xs].
Proof.
  intros m d n xs N L B W. split; [split|].
  - cbn. split; [exact L| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

Lemma mm_fwd : forall (m : word -> option byte) d p q x pre rest,
  0 <= q -> q + 1 <= 2^64 -> d + Z.of_nat (length pre) = q -> q <= p ->
  bytes_at asegs m d pre -> bytes_at asegs m p (x :: rest) ->
  bytes_at asegs (write_to_mem m (wa q) [x]) d (pre ++ [x]) /\
  bytes_at asegs (write_to_mem m (wa q) [x]) (p + 1) rest.
Proof.
  intros m d p q x pre rest Q0 Q1 Eq QP Bd Bp.
  change (x :: rest) with ([x] ++ rest) in Bp. apply bytes_at_app in Bp. destruct Bp as [_ Bp].
  change (Z.of_nat (length [x])) with 1 in Bp.
  split.
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact Bd| lia| cbn [length Z.of_nat Pos.of_succ_nat]; lia| left; lia].
    + rewrite Eq. apply bytes_at_write_same; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
  - apply bytes_at_write_other; [exact Bp| lia| cbn [length Z.of_nat Pos.of_succ_nat]; lia
                                | right; cbn [length Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Lemma mm_bwd : forall (m : word -> option byte) s q x pre post,
  0 <= q -> q + 1 <= 2^64 -> s + Z.of_nat (length pre) <= q ->
  bytes_at asegs m s (pre ++ [x]) -> bytes_at asegs m (q + 1) post ->
  bytes_at asegs (write_to_mem m (wa q) [x]) s pre /\
  bytes_at asegs (write_to_mem m (wa q) [x]) q (x :: post).
Proof.
  intros m s q x pre post Q0 Q1 SQ Bs Bp.
  apply bytes_at_app in Bs. destruct Bs as [Bs _].
  split.
  - apply bytes_at_write_other; [exact Bs| lia| cbn [length Z.of_nat Pos.of_succ_nat]; lia| left; lia].
  - change (x :: post) with ([x] ++ post). apply bytes_at_app. split.
    + apply bytes_at_write_same; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    + change (Z.of_nat (length [x])) with 1.
      apply bytes_at_write_other; [exact Bp| lia| cbn [length Z.of_nat Pos.of_succ_nat]; lia
                                  | right; cbn [length Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Ltac mm_norm m q x :=
  lazymatch goal with |- context [write_to_mem m ?a ?bs] =>
    replace (write_to_mem m a bs) with (write_to_mem m (wa q) [x])
      by (f_equal; first [ reflexivity | symmetry; exact (le1_zxb x) | unfold wa; f_equal; lia
                         | f_equal; symmetry; apply Z_to_bv_bv_unsigned ])
  end.

Lemma mm_at : forall (m : word -> option byte) a a' bs, bytes_at asegs m a bs -> a = a' -> bytes_at asegs m a' bs.
Proof. intros m a a' bs H E. subst a'. exact H. Qed.

Section Loops.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (d s n : Z) (xs : list byte) (m0 : word -> option byte).

Lemma imemmove_fwd : forall rest x pre (p q : Z) (a4 a5 a6 : word) (m : word -> option byte),
  pre ++ x :: rest = xs -> p = s + Z.of_nat (length pre) -> q = d + Z.of_nat (length pre) ->
  n = Z.of_nat (length xs) -> 0 <= d -> d < s -> s + n < 2^64 ->
  bytes_at asegs m d pre -> bytes_at asegs m p (x :: rest) -> wr_at asegs m d n ->
  munch [(d, d + n)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n xs m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 p) (Z_to_bv 64 (d + n)) (Z_to_bv 64 q) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x651bc) fc None m (seg_rom asegs)).
Proof.
  induction rest as [|y rest IH]; intros x pre p q a4 a5 a6 m EX Ep Eq En D0 DS SN Bd Bp W MU WM MI.
  - assert (LX : Z.of_nat (length xs) = Z.of_nat (length pre) + 1)
      by (rewrite <- EX, length_app; cbn [length]; lia).
    pose proof (mm_rd m p x [] Bp) as HR.
    pose proof (mm_st m d n q W ltac:(lia) ltac:(lia)) as HS.
    destruct (mm_fwd m d p q x pre [] ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd Bp) as [B1 _].
    pose proof (munch_write [(d, d + n)] m0 m q [x] MU ltac:(lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                  ltac:(cbn [inside length Z.of_nat Pos.of_succ_nat]; lia)) as MU1.
    pose proof (wmono_write asegs m0 m (wa q) [x] WM) as WM1.
    pose proof (mem_inv_store asegs m (wa q) [x] MI HS) as MI1.
    pose proof (wr_at_write asegs m d n (wa q) [x] W) as W1.
    assert (EUq : bv_unsigned (Z_to_bv 64 (q + 1)) = q + 1) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 (d + n)) = d + n) by (apply unsigned_lit; lia).
    lstep. lstep. lstep. lstep. lstep. if_false. lstep. lstep.
    mm_norm m q x.
    sys_finish.
    apply mm_rw_intro; [lia| lia| rewrite <- EX; exact B1| exact W1].
  - assert (LX : Z.of_nat (length xs) = Z.of_nat (length pre) + 2 + Z.of_nat (length rest))
      by (rewrite <- EX, length_app; cbn [length]; lia).
    pose proof (mm_rd m p x (y :: rest) Bp) as HR.
    pose proof (mm_st m d n q W ltac:(lia) ltac:(lia)) as HS.
    destruct (mm_fwd m d p q x pre (y :: rest) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd Bp) as [B1 B2].
    pose proof (munch_write [(d, d + n)] m0 m q [x] MU ltac:(lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                  ltac:(cbn [inside length Z.of_nat Pos.of_succ_nat]; lia)) as MU1.
    pose proof (wmono_write asegs m0 m (wa q) [x] WM) as WM1.
    pose proof (mem_inv_store asegs m (wa q) [x] MI HS) as MI1.
    pose proof (wr_at_write asegs m d n (wa q) [x] W) as W1.
    assert (EUq : bv_unsigned (Z_to_bv 64 (q + 1)) = q + 1) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 (d + n)) = d + n) by (apply unsigned_lit; lia).
    lstep. lstep. lstep. lstep. lstep. if_true.
    mm_norm m q x.
    eapply (IH y (pre ++ [x]));
      [ rewrite <- app_assoc; exact EX
      | rewrite length_app; cbn [length]; lia
      | rewrite length_app; cbn [length]; lia
      | exact En| lia| lia| lia| exact B1
      | lazymatch goal with |- bytes_at _ _ ?a _ => replace a with (p + 1) by lia; exact B2 end
      | exact W1| exact MU1| exact WM1| exact MI1 ].
Qed.

Lemma imemmove_bwd : forall pre x post (j : Z) (a4 a5 a6 : word) (m : word -> option byte),
  pre ++ x :: post = xs -> j = Z.of_nat (length pre) ->
  n = Z.of_nat (length xs) -> 0 <= s -> s < d -> d + n < 2^64 ->
  bytes_at asegs m s (pre ++ [x]) -> bytes_at asegs m (d + j + 1) post -> wr_at asegs m d n ->
  munch [(d, d + n)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n xs m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 1) (Z_to_bv 64 j) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x651e4) fc None m (seg_rom asegs)).
Proof.
  intros pre. induction pre as [|y pre IH] using rev_ind;
    intros x post j a4 a5 a6 m EX Ej En S0 SD DN Bs Bp W MU WM MI.
  - assert (HR : ov_read_bytes asegs m (Z_to_bv 64 (s + j)) 1 = Some [x]) by (rewrite Ej; exact (mm_last m s x [] Bs)).
    cbn [length Z.of_nat] in Ej.
    assert (LX : Z.of_nat (length xs) = Z.of_nat (length post) + 1)
      by (rewrite <- EX; cbn [app length]; lia).
    pose proof (mm_st m d n (d + j) W ltac:(lia) ltac:(lia)) as HS.
    destruct (mm_bwd m s (d + j) x [] post ltac:(lia) ltac:(lia) ltac:(cbn [length Z.of_nat]; lia) Bs Bp) as [_ B2].
    pose proof (munch_write [(d, d + n)] m0 m (d + j) [x] MU ltac:(lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                  ltac:(cbn [inside length Z.of_nat Pos.of_succ_nat]; lia)) as MU1.
    pose proof (wmono_write asegs m0 m (wa (d + j)) [x] WM) as WM1.
    pose proof (mem_inv_store asegs m (wa (d + j)) [x] MI HS) as MI1.
    pose proof (wr_at_write asegs m d n (wa (d + j)) [x] W) as W1.
    assert (EUj : bv_unsigned (Z_to_bv 64 (j + 1)) = j + 1) by (apply unsigned_lit; lia).
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. if_false. lstep.
    mm_norm m (d + j) x.
    sys_finish.
    apply mm_rw_intro; [lia| lia| | exact W1].
    rewrite <- EX. cbn [app]. apply (mm_at _ (d + j) d _ B2). lia.
  - assert (HR : ov_read_bytes asegs m (Z_to_bv 64 (s + j)) 1 = Some [x])
      by (rewrite Ej; exact (mm_last m s x (pre ++ [y]) Bs)).
    rewrite length_app in Ej. cbn [length] in Ej.
    assert (LX : Z.of_nat (length xs) = Z.of_nat (length pre) + 2 + Z.of_nat (length post))
      by (rewrite <- EX, !length_app; cbn [length]; lia).
    pose proof (mm_st m d n (d + j) W ltac:(lia) ltac:(lia)) as HS.
    destruct (mm_bwd m s (d + j) x (pre ++ [y]) post ltac:(lia) ltac:(lia)
                ltac:(rewrite length_app; cbn [length]; lia) Bs Bp) as [B1 B2].
    pose proof (munch_write [(d, d + n)] m0 m (d + j) [x] MU ltac:(lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                  ltac:(cbn [inside length Z.of_nat Pos.of_succ_nat]; lia)) as MU1.
    pose proof (wmono_write asegs m0 m (wa (d + j)) [x] WM) as WM1.
    pose proof (mem_inv_store asegs m (wa (d + j)) [x] MI HS) as MI1.
    pose proof (wr_at_write asegs m d n (wa (d + j)) [x] W) as W1.
    assert (EUj : bv_unsigned (Z_to_bv 64 (j + 1)) = j + 1) by (apply unsigned_lit; lia).
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. if_true.
    mm_norm m (d + j) x.
    eapply (IH y (x :: post));
      [ rewrite <- app_assoc in EX; exact EX
      | lia| exact En| lia| lia| lia| exact B1
      | lazymatch goal with |- bytes_at _ _ ?a _ => replace a with (d + j) by lia; exact B2 end
      | exact W1| exact MU1| exact WM1| exact MI1 ].
Qed.

End Loops.

Theorem imemmove_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (d s n : Z) (xs junk : list byte),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n ->
  0 <= n <= 2^40 -> d + n < 2^64 -> s + n < 2^64 -> length xs = Z.to_nat n ->
  bytes_at asegs m s xs -> rw_cells asegs m d [CB (Z.to_nat n) junk] -> mem_inv asegs m ->
  evt asegs (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n xs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x651ac) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> -> -> N DN SN L SRC DST MI.
  pose proof (bytes_at_bound asegs m s xs SRC) as SB.
  pose proof (mm_wr_of_rw m d n junk ltac:(lia) DST) as W. clear DST.
  pose proof W as (D0 & _ & _).
  pose proof (munch_refl [(d, d + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (ESn : bv_signed (Z_to_bv 64 n) = n) by (rewrite zb_signed, EUn; destruct (Z.ltb_spec n (2^63)); lia).
  assert (Ln : n = Z.of_nat (length xs)) by lia.
  destruct (Z_lt_le_dec d s) as [DS|SD].
  - lstep. if_false.
    destruct (Z.eq_dec n 0) as [N0|N0].
    + lstep. if_true. lstep.
      sys_finish.
      apply mm_rw_intro; [lia| exact L| | exact W].
      destruct xs; [apply bytes_at_nil; lia| cbn [length] in L; lia].
    + lstep. if_false. lstep. lstep.
      destruct xs as [|x rest]; [cbn [length] in L; lia|].
      eapply imemmove_fwd with (rest := rest) (x := x) (pre := []) (s := s);
        [ reflexivity| cbn [length Z.of_nat]; lia| cbn [length Z.of_nat]; lia| exact Ln| lia| lia| lia
        | apply bytes_at_nil; lia| exact SRC| exact W| exact MU| exact WM| exact MI ].
  - lstep. if_true.
    destruct (Z.eq_dec s d) as [E|E].
    + lstep. if_true. lstep.
      sys_finish.
      apply mm_rw_intro; [lia| exact L| subst s; exact SRC| exact W].
    + lstep. if_false.
      destruct (Z.eq_dec n 0) as [N0|N0].
      * lstep. if_true. lstep.
        sys_finish.
        apply mm_rw_intro; [lia| exact L| | exact W].
        destruct xs; [apply bytes_at_nil; lia| cbn [length] in L; lia].
      * lstep. if_false. lstep. lstep.
        assert (NE : xs <> []) by (intros ->; cbn [length] in L; lia).
        destruct (@exists_last _ xs NE) as (pre & x & Exs).
        assert (LP : Z.of_nat (length xs) = Z.of_nat (length pre) + 1)
          by (rewrite Exs, length_app; cbn [length]; lia).
        eapply imemmove_bwd with (pre := pre) (x := x) (post := []) (s := s);
          [ symmetry; exact Exs| lia| exact Ln| lia| lia| lia
          | rewrite <- Exs; exact SRC| apply bytes_at_nil; lia| exact W| exact MU| exact WM| exact MI ].
Qed.
