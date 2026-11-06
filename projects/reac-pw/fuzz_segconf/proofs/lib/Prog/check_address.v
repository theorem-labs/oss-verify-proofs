From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strlen_c strncmp_c check_address_c.
Import ListNotations.
Open Scope Z_scope.

(** check_address of the plain image (0x14964, 19 instructions),
    from strlen_contract (0x1ec30) and strncmp_contract (0x1ed84), walked with Lib/Tac.v and Lib/Step.v.
    The prologue carves the 32-byte frame and saves ra, s0, s1 in it; s0 = want, s1 = got. strlen(want) is called
    with want's bytes, its NUL and the slack up to the next 8-byte boundary (cstr_at), cut to exactly that slack so
    the frame stores cannot touch it; it returns length ws. strncmp(got, want, length ws) is called with got's bytes
    and NUL (cstrz_at) and want's bytes, NUL and slack: [strncmp_model_cstr] gives StrFun.strncmp_model on these lists
    as SegModel.strncmp on the strings, which the premise makes 0, so `bnez a0` falls through and the `jal abort` at
    0x149ac is dead. The epilogue reloads ra, s0, s1 and frees the frame. *)

(** ** The bridges from the callee contracts' byte-list models to the spine's SegModel *)

(** A string with no NUL byte: SegModel.strlen of its values is its length. *)
Lemma bridge_strlen : forall str : list byte, ~ In (Z_to_bv 8 0) str -> SegModel.strlen (zs str) = length str.
Proof.
  intros str H. rewrite strlen_id.
  - unfold zs. apply length_map.
  - intros Hin. apply H. unfold zs in Hin. apply in_map_iff in Hin as (b & Hb & Hin).
    replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(** The byte form of a NUL-free value list. *)
Lemma nul_free_bytes : forall bs : list byte, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof. intros bs H Hin. apply H. unfold zs. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

(** StrFun.strncmp_walk on two C strings (got's bytes and NUL; want's bytes, NUL and any slack) is SegModel's
    strncmp_go on their values, for every count k: the walk never runs off a list, since each NUL stops it. *)
Lemma walk_bridge : forall (bg bw sl : list byte) (k : nat),
  ~ In 0 (zs bg) -> ~ In 0 (zs bw) ->
  strncmp_walk (bg ++ [ZERO]) (bw ++ ZERO :: sl) k = Some (strncmp_go (zs bg) (zs bw) k).
Proof.
  unfold zs.
  induction bg as [|x bg IH]; intros bw sl k NG NW.
  - destruct bw as [|y bw]; destruct k; reflexivity.
  - cbn [map In] in NG. assert (Hx : bv_unsigned x <> 0) by tauto.
    assert (NG' : ~ In 0 (map bv_unsigned bg)) by tauto.
    destruct bw as [|y bw].
    + cbn [app map strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Hx). destruct k; reflexivity.
    + cbn [map In] in NW. assert (Hy : bv_unsigned y <> 0) by tauto.
      assert (NW' : ~ In 0 (map bv_unsigned bw)) by tauto.
      destruct k as [|k].
      * cbn [app map strncmp_walk strncmp_go hd0].
        rewrite (proj2 (Z.eqb_neq _ _) Hx), (proj2 (Z.eqb_neq _ _) Hy). reflexivity.
      * cbn [app map strncmp_walk strncmp_go].
        rewrite !(proj2 (Z.eqb_neq _ _) Hx), !(proj2 (Z.eqb_neq _ _) Hy).
        destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E]; cbn [negb orb andb Nat.eqb].
        -- apply IH; assumption.
        -- reflexivity.
Qed.

(** The model strncmp's contract takes, on the lists this walk passes and n = the length of want: it exists, and it
    is SegModel.strncmp on the two strings. *)
Lemma strncmp_model_cstr : forall (bg bw sl : list byte),
  ~ In 0 (zs bg) -> ~ In 0 (zs bw) ->
  strncmp_model (bg ++ [ZERO]) (bw ++ ZERO :: sl) (Z.of_nat (length bw)) =
  Some (SegModel.strncmp (zs bg) (zs bw) (length bw)).
Proof.
  intros bg bw sl NG NW. unfold strncmp_model.
  destruct (length bw) as [|n] eqn:L.
  - reflexivity.
  - replace (Z.to_nat (Z.of_nat (S n) - 1)) with n by lia.
    change (Z.of_nat (S n) =? 0) with false. unfold SegModel.strncmp. cbv iota beta.
    apply walk_bridge; assumption.
Qed.

Lemma bytes_at_prefix : forall segs m a (l1 l2 : list byte), bytes_at segs m a (l1 ++ l2) -> bytes_at segs m a l1.
Proof. intros segs m a l1 l2 H. apply bytes_at_app in H. destruct H as [H _]. exact H. Qed.

(** A branch whose condition the context decides. *)
Ltac br := first [ if_false | if_true | idtac ].

Theorem check_address_holds : strlen_contract -> strncmp_contract -> check_address_contract.
Proof.
  intros SL SN. unfold strlen_contract in SL. unfold strncmp_contract in SN.
  unfold check_address_contract, check_address_pre, CHECK_ADDRESS, CHECK_ADDRESS_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo gs ws
    (G0 & (bg & BG & ZG & NG) & GA & W0 & (bw & sl & BW & ZW & NW & SLK) & WA & CMP & (ST & D32 & SP16 & ROM) & MI).
  subst gs ws. clear ROM G0 W0.
  assert (Lzg : length (zs bg) = length bg) by (unfold zs; apply length_map).
  assert (Lzw : length (zs bw) = length bw) by (unfold zs; apply length_map).
  rewrite Lzg in GA. rewrite Lzw in WA, SLK. unfold apart in GA, WA.
  pose proof (nul_free_bytes _ NW) as NWb.
  rewrite (bridge_strlen bw NWb) in CMP.
  pose proof (bytes_at_bound _ _ _ _ BW) as BWb. rewrite length_app in BWb. cbn [length] in BWb.
  pose proof (bytes_at_bound _ _ _ _ BG) as BGb. rewrite length_app in BGb. cbn [length] in BGb.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* the slack strlen reads: exactly the bytes up to the next 8-byte boundary *)
  pose proof (Z.mod_pos_bound (- (bv_unsigned a1 + Z.of_nat (length bw) + 1)) 8 ltac:(lia)) as K8b.
  remember ((- (bv_unsigned a1 + Z.of_nat (length bw) + 1)) mod 8) as K8 eqn:EK.
  assert (SL' : exists sl', bytes_at rsegs m (bv_unsigned a1) (bw ++ ZERO :: sl') /\ Z.of_nat (length sl') = K8).
  { exists (firstn (Z.to_nat K8) sl). split.
    - apply (bytes_at_prefix _ _ _ _ (skipn (Z.to_nat K8) sl)).
      rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. exact BW.
    - rewrite length_firstn. lia. }
  clear BW. destruct SL' as (sl' & BW & Lsl).
  assert (SLK2 : (- (bv_unsigned a1 + Z.of_nat (length bw) + 1)) mod 8 <= Z.of_nat (length sl')) by (rewrite <- EK; lia).
  (* both strings lie apart from the frame [sp - 32, sp) *)
  assert (DW : bv_unsigned a1 + Z.of_nat (length bw) + 1 + Z.of_nat (length sl') <= bv_unsigned sp - 32
               \/ bv_unsigned sp <= bv_unsigned a1).
  { clear - WA D32 SP16 Lsl EK. rewrite Lsl. subst K8. destruct WA as [H|H]; [left | right; exact H].
    Z.div_mod_to_equations. lia. }
  assert (DG : bv_unsigned a0 + Z.of_nat (length bg) + 1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)
    by lia.
  clear GA WA SP16 EK K8b SLK Lsl BWb. clear K8.
  pose proof (bytes_at_bound _ _ _ _ BW) as BWb. rewrite length_app in BWb. cbn [length] in BWb.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* addi sp, sp, -32; sd ra, 24(sp); sd s0, 16(sp); sd s1, 8(sp); mv s0, a1; mv s1, a0; mv a0, a1; jal strlen *)
  do 8 step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply SL with (str := bw) (slack := sl') | post_call segs mm]
  end;
  [ exact BW | exact NWb | exact SLK2 | assumption | ].
  (* mv a2, a0; mv a0, s1; mv a1, s0; jal strncmp *)
  do 4 step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply SN with (ls := bg ++ [ZERO]) (rs := bw ++ ZERO :: sl') (v := 0) | post_call segs mm]
  end;
  [ exact BG | exact BW | | assumption | ].
  { rewrite unsigned_lit by lia. rewrite strncmp_model_cstr by assumption. rewrite CMP. reflexivity. }
  (* bnez a0: a0 = 0, not taken; ld ra; ld s0; ld s1; addi sp, sp, 32 *)
  step. br.
  do 4 step.
  release_frame FR ST (bv_unsigned sp).
  (* ret *)
  step.
  finish.
  all: try exact I.
Qed.
