(** * ItGPfWin — pairwise prefix-freeness at the WINDOW list, straight
    from the dispatch's PreGo over the CONCATENATED array.

    OWNER: an earlier development run.  The B3 heads hand the assembly
    [it_pre ty (zlens (lit ++ dst)) (Z.of_nat (length lit)) root0 t0
       = PreGo c st] — the array is the WHOLE header list, the count is
    the window.  two_own_v3_of_parts (ItGWidth.v) wants pairwise
    prefix-freeness AT THE WINDOW LIST [lit].  This file is that bridge:
    it_pre reads the array only on [0, codes), so its accept verdict IS
    the window list's accept verdict (counts_of_it_count_agree), and
    acceptance gives ValidLengths gives canonical_prefix_free — all
    landed InftreesBridge/Huff machinery, composed once.

    Kept as its own file so ItGWidth.v keeps its minimal Base/Bits/Huff
    import surface.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees InftreesBridge.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The concatenated array agrees with the window list on the window. *)
Lemma zlens_app_window : forall (l1 l2 : list nat),
  arr_eq_on (zlens (l1 ++ l2)) (zlens l1) 0 (Z.of_nat (length l1)).
Proof.
  intros l1 l2 i Hi. unfold zlens. f_equal.
  apply app_nth1. lia.
Qed.

(** PreGo over the concatenated array, prefix-freeness at the window. *)
Theorem window_codes_prefix_free :
  forall ty (l1 l2 : list nat) root0 t0 c st s1 s2 cw1 cw2,
    (forall len, In len l1 -> (len <= 15)%nat) ->
    it_pre ty (zlens (l1 ++ l2)) (Z.of_nat (length l1)) root0 t0
      = PreGo c st ->
    code_for l1 15%nat s1 = Some cw1 ->
    code_for l1 15%nat s2 = Some cw2 ->
    s1 <> s2 ->
    is_prefix cw1 cw2 = false.
Proof.
  intros ty l1 l2 root0 t0 c st s1 s2 cw1 cw2 Hle Hpre H1 H2 Hs.
  destruct (it_pre_go_inv ty (zlens (l1 ++ l2)) (Z.of_nat (length l1))
              root0 t0 c st Hpre) as (_ & _ & Hacc).
  assert (HC : CountsOf (it_cnt0 (zlens (l1 ++ l2)) (Z.of_nat (length l1)))
                 l1 15%nat).
  { apply (counts_of_it_count_agree _ _ l1 15%nat eq_refl).
    apply zlens_app_window. }
  pose proof (it_accept_valid _ _ _ l1 Hle HC Hacc) as HV.
  exact (canonical_prefix_free l1 15%nat s1 s2 cw1 cw2 HV H1 H2 Hs).
Qed.
