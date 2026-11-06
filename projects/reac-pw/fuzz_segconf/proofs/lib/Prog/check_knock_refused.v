(** check_knock_refused of the plain image (0x149b0, 11 instructions, 16-byte frame; image 3776ca44d75c): proof of
    [check_knock_refused_contract]
    (check_knock_refused_c.v) from strstr's contract (strstr_c.v, STRSTR = 0x1f0c4).

    Shape: `addi sp,sp,-16; sd ra,8(sp)`; `beqz a1` (k = false) goes to the epilogue 0x149cc; else
    a1 = 0x10433 (seg_spec.STR_TNP, "takes no plan"), `jal strstr` at sp' = sp - 16, `beqz a0` to `jal abort`
    (0x149d8), else the epilogue `ld ra,8(sp); addi sp,sp,16; ret`. The abort is dead: with k = true the premise
    gives strstr_found gs TNP = true, so strstr returns a nonzero word ([bridge_strstr], [ckr_val_range]).

    strstr's premises at sp': the haystack is cstr_at's bytes with the slack cut to its first
    (-(got + |gs| + 1)) mod 8 bytes, so that a haystack below lo stays below sp' - 2256 ([ckr_pad_le]:
    sp - 2272 is a multiple of 8); the needle is the image's 14 read-only bytes at STR_TNP ([ckr_tnp_at]), apart
    from the stack because stack_ok makes [lo, sp) non-image ([ckr_ro_apart]); the GOT cell and guard are
    sa_got_guard / sa_guard of SEG_PLAIN, which are twoway_strstr_c's GOT_GUARD / GUARD. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel StrStr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec twoway_strstr_c strstr_c
  check_knock_refused_c.
Import ListNotations.
Open Scope Z_scope.

(** ** StrStr's search and SegModel.strstr_found *)
Lemma ckr_prefix : forall nd h, prefix_eqb nd h = prefixb nd h.
Proof. induction nd as [|a nd IH]; intros [|b h]; cbn; try rewrite IH; reflexivity. Qed.

Lemma ckr_ff_infix : forall h nd, find_first h nd <> None <-> infixb nd h = true.
Proof.
  induction h as [|x h IH]; intros nd; cbn [find_first infixb]; rewrite ckr_prefix.
  - destruct (prefixb nd []); cbn [orb].
    + split; intros _; [reflexivity | discriminate].
    + split; intros H; [exfalso; apply H; reflexivity | discriminate].
  - destruct (prefixb nd (x :: h)); cbn [orb].
    + split; intros _; [reflexivity | discriminate].
    + specialize (IH nd). destruct (find_first h nd) as [i|]; cbn [option_map].
      * split; intros _; [apply IH; discriminate | discriminate].
      * split; intros H; [exfalso; apply H; reflexivity | apply IH in H; exfalso; apply H; reflexivity].
Qed.

Lemma ckr_ff_bound : forall h nd i, find_first h nd = Some i -> (i <= length h)%nat.
Proof.
  induction h as [|x h IH]; intros nd i H; cbn [find_first] in H.
  - destruct (prefix_eqb nd []); [inversion H; subst; cbn; lia | discriminate].
  - destruct (prefix_eqb nd (x :: h)); [inversion H; subst; cbn [length]; lia |].
    destruct (find_first h nd) as [j|] eqn:E; cbn [option_map] in H; [|discriminate].
    inversion H; subst. apply IH in E. cbn [length]. lia.
Qed.

Lemma ckr_nonul : forall bs, ~ In ZERO bs -> nulfree (zs bs).
Proof.
  intros bs H Hin. unfold zs in Hin. apply in_map_iff in Hin as [b [Hb Hin]]. apply H.
  replace ZERO with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma ckr_nonul_b : forall bs, nulfree (zs bs) -> ~ In ZERO bs.
Proof. intros bs H Hin. apply H. unfold zs. change 0 with (bv_unsigned ZERO). apply in_map. exact Hin. Qed.

(** strstr's answer is nonzero exactly when the needle occurs in the haystack (A > 0; hb, nb NUL-free). *)
Lemma bridge_strstr : forall A hb nb, 0 < A -> ~ In ZERO hb -> ~ In ZERO nb ->
  (strstr_val A hb nb <> 0 <-> strstr_found (zs hb) (zs nb) = true).
Proof.
  intros A hb nb HA Hh _. unfold strstr_found. rewrite (cut_nul_id _ (ckr_nonul hb Hh)).
  pose proof (ckr_ff_infix (zs hb) (zs nb)) as FI. unfold strstr_val.
  change (map bv_unsigned hb) with (zs hb). change (map bv_unsigned nb) with (zs nb).
  revert FI. destruct (find_first (zs hb) (zs nb)) as [i|]; intros FI; split; intros H.
  - apply FI. discriminate.
  - lia.
  - exfalso. apply H. reflexivity.
  - apply FI in H. exfalso. apply H. reflexivity.
Qed.

(** strstr's answer is a word: 0 or A + i with i <= |hb|. *)
Lemma ckr_val_range : forall A hb nb, 0 <= A -> A + Z.of_nat (length hb) < 2^64 ->
  0 <= strstr_val A hb nb < 2^64.
Proof.
  intros A hb nb H0 H1. unfold strstr_val.
  destruct (find_first (map bv_unsigned hb) (map bv_unsigned nb)) as [i|] eqn:E; [|lia].
  apply ckr_ff_bound in E. rewrite length_map in E. lia.
Qed.

(** ** Arithmetic and bytes *)
(** Rounding x up to a multiple of 8 stays at or below a multiple of 8 above x. *)
Lemma ckr_pad_le : forall x y, x <= y -> y mod 8 = 0 -> x + (- x) mod 8 <= y.
Proof. intros x y H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma ckr_trunc : forall m a l1 (x : byte) l2 k, bytes_at rsegs m a (l1 ++ x :: l2) ->
  bytes_at rsegs m a (l1 ++ x :: firstn k l2).
Proof.
  intros m a l1 x l2 k H.
  replace (l1 ++ x :: l2) with ((l1 ++ x :: firstn k l2) ++ skipn k l2) in H
    by (rewrite <- app_assoc; cbn [app]; rewrite firstn_skipn; reflexivity).
  apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma ckr_nf_dec : forall l, forallb (fun x => negb (x =? 0)) l = true -> nulfree l.
Proof.
  induction l as [|a l IH]; intros H Hin; [exact Hin|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. cbn [In] in Hin.
  destruct Hin as [E|Hin]; [subst a; cbn in H1; discriminate H1 | exact (IH H2 Hin)].
Qed.

(** Read-only image bytes lie wholly outside a non-image range. *)
Lemma ckr_ro_apart : forall A bs lo hi, ro_bytes rsegs A bs -> bs <> [] -> lo < hi ->
  (forall a, lo <= a < hi -> seg_rom rsegs (wa a) = None) -> A + Z.of_nat (length bs) <= lo \/ hi <= A.
Proof.
  intros A bs lo hi R Hne Hlh H.
  assert (LB : (0 < length bs)%nat) by (destruct bs; [exfalso; apply Hne; reflexivity | cbn; lia]).
  destruct (Z.le_gt_cases (A + Z.of_nat (length bs)) lo) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases hi A) as [G|G]; [right; exact G|]. exfalso.
  destruct (nth_error bs (Z.to_nat (Z.max A lo - A))) as [b|] eqn:E.
  - pose proof (ro_bytes_nth rsegs bs A _ b R E) as [RB _].
    replace (A + Z.of_nat (Z.to_nat (Z.max A lo - A))) with (Z.max A lo) in RB by lia.
    rewrite (H (Z.max A lo)) in RB by lia. discriminate.
  - apply nth_error_None in E. lia.
Qed.

(** ** The needle "takes no plan" at STR_TNP in the image *)
Definition TNP_B : list byte := zb TNP.

Lemma ckr_tnp_ro : ro_bytes_b rsegs STR_TNP (TNP_B ++ [Z_to_bv 8 0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ckr_tnp_len : length TNP_B = 13%nat.
Proof. reflexivity. Qed.
Lemma ckr_tnp_zs : zs TNP_B = TNP.
Proof. vm_compute. reflexivity. Qed.
Lemma ckr_tnp_nonul : ~ In ZERO TNP_B.
Proof. apply ckr_nonul_b. rewrite ckr_tnp_zs. apply ckr_nf_dec. vm_compute. reflexivity. Qed.

Lemma ckr_tnp_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10433 (TNP_B ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI | lia | rewrite length_app, ckr_tnp_len; cbn [length]; lia |].
  exact (ro_bytes_b_sound rsegs _ STR_TNP ckr_tnp_ro).
Qed.

Lemma ckr_tnp_apart : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> seg_rom rsegs (wa a) = None) ->
  0x10433 + 14 <= lo \/ hi <= 0x10433.
Proof.
  intros lo hi Hlh H.
  pose proof (ckr_ro_apart STR_TNP (TNP_B ++ [Z_to_bv 8 0]) lo hi (ro_bytes_b_sound rsegs _ STR_TNP ckr_tnp_ro)
                ltac:(intros E; apply app_eq_nil in E; destruct E as [_ E]; discriminate E) Hlh H) as X.
  rewrite length_app, ckr_tnp_len in X. cbn [length] in X. unfold STR_TNP in X. lia.
Qed.

(** ** The walk *)
Theorem check_knock_refused_holds : strstr_contract -> check_knock_refused_contract.
Proof.
  intros SS. unfold check_knock_refused_contract, CHECK_KNOCK_REFUSED, CHECK_KNOCK_REFUSED_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo gs k
    PRE.
  unfold check_knock_refused_pre, CHECK_KNOCK_REFUSED_STACK in PRE.
  destruct PRE as (G0 & CS & AP & KN & KF & GOT & [g GD] & GL & GTL & SOK & MI).
  destruct SOK as (ST & DEP & SPA & NR).
  change (sa_got_guard SEG_PLAIN) with GOT_GUARD in GOT, GTL.
  change (sa_guard SEG_PLAIN) with GUARD in GOT, GD, GL.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* the haystack, its slack cut to the first pad bytes *)
  destruct CS as (hb & sl & HB & ZS & NZ & PAD).
  assert (LH : length hb = length gs) by (rewrite <- ZS; unfold zs; rewrite length_map; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB. rewrite length_app in HBB. cbn [length] in HBB.
  remember ((- (bv_unsigned a0 + Z.of_nat (length gs) + 1)) mod 8) as P eqn:EP.
  assert (PR : 0 <= P < 8) by (rewrite EP; apply Z.mod_pos_bound; lia).
  pose proof (ckr_trunc m _ hb ZERO sl (Z.to_nat P) HB) as HB2. clear HB.
  assert (HL : Z.of_nat (length (firstn (Z.to_nat P) sl)) = P) by (rewrite length_firstn; lia).
  assert (Y8 : (bv_unsigned sp - 2272) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
  assert (HAP : bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length (firstn (Z.to_nat P) sl))
                  <= bv_unsigned sp - 2272 \/ bv_unsigned sp <= bv_unsigned a0).
  { rewrite LH, HL. destruct AP as [AP|AP]; [left | right; lia].
    pose proof (ckr_pad_le (bv_unsigned a0 + Z.of_nat (length gs) + 1) (bv_unsigned sp - 2272) ltac:(lia) Y8)
      as PL.
    rewrite EP. lia. }
  assert (HPAD : (- (bv_unsigned a0 + Z.of_nat (length hb) + 1)) mod 8
                   <= Z.of_nat (length (firstn (Z.to_nat P) sl))) by (rewrite LH, HL, <- EP; lia).
  assert (NH : ~ In ZERO hb) by (apply ckr_nonul_b; rewrite ZS; exact NZ).
  pose proof (ckr_tnp_apart lo (bv_unsigned sp) ltac:(lia) NR) as NAP.
  clear AP PAD SPA Y8 NR.
  pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* addi sp,sp,-16; sd ra,8(sp) *)
  zstep. carve_frame 16%nat ST.
  zstep.
  (* beqz a1 *)
  zstep.
  destruct k; cbn [b2z] in KN.
  - (* k = true: a1 = 1, the strstr call *)
    let K := fresh "K" in if_cases K; [exfalso; zify_cond K; lia | clear K].
    cbn [negb orb] in KF. rewrite <- ZS, <- ckr_tnp_zs in KF.
    pose proof (proj2 (bridge_strstr (bv_unsigned a0) hb TNP_B ltac:(lia) NH ckr_tnp_nonul) KF) as NZV.
    pose proof (ckr_val_range (bv_unsigned a0) hb TNP_B ltac:(lia) ltac:(lia)) as RV.
    (* auipc a1; addi a1 (a1 = 0x10433); jal strstr *)
    do 3 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (ckr_tnp_at mm MI) as NB end.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SS with (hb := hb) (hs := firstn (Z.to_nat P) sl) (nb := TNP_B) (g := g)
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; unfold strstr_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
        post_call segs mm ]
    end;
    [ rewrite ?unsigned_lit by lia; exact ST
    | rewrite ?unsigned_lit by lia; lia
    | exact HB2
    | exact NH
    | exact HPAD
    | exact G0
    | rewrite ?unsigned_lit by lia; exact NB
    | exact ckr_tnp_nonul
    | exact MI
    | rewrite ?unsigned_lit by lia; lia
    | rewrite ?unsigned_lit by lia; rewrite ckr_tnp_len; lia
    | exact GOT
    | exact GD
    | rewrite ?unsigned_lit by lia; lia
    | rewrite ?unsigned_lit by lia; lia
    | ].
    match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
    (* beqz a0: strstr found the needle, a0 <> 0 *)
    zstep.
    let K := fresh "K" in if_cases K;
      [ exfalso; zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite ?unsigned_lit_wrap in K;
        clear - K RV NZV; Z.div_mod_to_equations; lia
      | clear K ].
    (* ld ra,8(sp); addi sp,sp,16; ret *)
    zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish; try exact I.
  - (* k = false: a1 = 0, straight to the epilogue *)
    let K := fresh "K" in if_cases K; [clear K | exfalso; zify_cond K; lia].
    zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish; try exact I.
Qed.
