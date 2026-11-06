(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 741 of its 860 lines of code are new or changed and 892 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R2.v, with its module paths, module names and addresses changed; 1878 of its 2027 lines of code are new or changed and 711 lines of the source are left out. *)
(* Segment R1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81414, 0x814f4] with the out-of-line
   stubs 0x82c14-0x82c24 and 0x82ca0-0x82ca8, Inv_A81414 -> Inv_A814f8 (R2) / Inv_A81b14 (P3).
   rule 24: no function proved (a slot segment).  R1 owns the our[] byte-scan loop: the inner fuzz_u8 arm
   (0x81414 .. 0x8143c) and the outer back edge 0x81488 -> 0x81400 -> 0x81414, six turns t = 0 .. 5, proved by
   induction on 5 - t inside this lemma.  Each turn stores our[t] = in[t] (left > 0) or 0 (left = 0) after the
   inline shadow checks (OUR: S(our + t) = 06 at S(fr) + 328; IN: the input block's shadow), so the three
   instrumented error calls 0x814a0, 0x82ca0, 0x82ca8 are not reached.  After turn 5 the tail reads the mode byte
   in[6] (IN again, error call 0x82c24 not reached), leaves to P3 on the left = 0 arm (0x81984) and on the
   even-mode arm (0x814cc), and on the odd-mode arm spills six frame pointers to [A + 48, A + 136), marks the
   catalogue count cell usable (S(fr) + 332 = 00), zeroes it and calls reac_box_catalogue (CAT@0x814f4).
   The write set of the odd-mode arm is our[] + [A + 48, A + 64) + [A + 72, A + 96) + [A + 128, A + 136) +
   S(fr) + 332 + [fr + 2656, fr + 2664) + the callee window [sp - 16, sp); of every other arm, our[] alone. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

Module RBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.

(* ---- small generic helpers (byte lists, readability, shadow and stack transports) ---- *)

Lemma r1_le1_lit : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite lib.Lib.MState.unsigned_lit by lia. reflexivity. Qed.

Lemma r1_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* A one-byte store `sb r,o(s3)` writes `le1 r`; the engine records it in the cells once it is a byte list. *)
Ltac r1_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (r1_le1_lit z) by lia; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (r1_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac r1_sb := step; r1_fix.

Lemma r1_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r1_ba_sub : forall m A bs k j, bytes_at rsegs m A bs -> (k + j <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma r1_rd_rw : forall m A n l x, rw_cells rsegs m A [CB n l] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A n l x ((Hwf & Hb) & _) Hx. cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hb.
  rewrite app_nil_r in Hb. destruct Hwf as (Hl & _).
  apply (r1_ba_rd m A l x Hb). rewrite Hl. exact Hx.
Qed.

(* r1_shadow_rw for any shadow region P the caller holds (route (C)); the run reads no shadow byte, so it has no
   region of its own. A LOCAL transport twin, since no A.ShadowRwOnT / A.ShadowRwOnK lemma fits: its side condition
   is, per shadow byte a, `outside W a \/ exists b, mrd rsegs m' (wa a) = Some b`, which is weaker than
   fl_shadow_rw_on's `outside W` for every shadow byte, than shadow_rw_on_kept's meta_kept (mrd unchanged at every
   shadow byte) and than shadow_rw_on_mem_mono's rd_mono (every present byte stays present). *)
Lemma r1_shadow_rw_on : forall W m m', munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros W m m' MU WM H P HS a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r1_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H.
  exact (A.ShadowRwOn.shadow_rw_of_on_all m'
           (r1_shadow_rw_on W m m' MU WM H _ (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HS))).
Qed.

Lemma r1_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r1_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma r1_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r1_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* A written byte is in the head interval or written by the rest: peels a write set one interval at a time, so
   lia never sees the negation of a long conjunction (exponential in its CNF). *)
Lemma r1_notout_cons : forall lo hi W x, ~ outside ((lo, hi) :: W) x -> (lo <= x < hi) \/ ~ outside W x.
Proof.
  intros lo hi W x H. destruct (r1_out_dec W x) as [Ho|Hno]; [left|right; exact Hno].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [exfalso; apply H; cbn [outside]; split; [lia | exact Ho]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [lia | exfalso; apply H; cbn [outside]; split; [lia | exact Ho]].
Qed.

Lemma r1_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma r1_sh8 : forall fr k, shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof.
  intros fr k. unfold shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes. *)
Lemma r1_addr_z : forall m p (z : nat) n, n = 8 * Z.of_nat z -> 0 <= p -> p mod 8 = 0 -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) z) -> addressable m p n.
Proof.
  intros m p z n -> Hp Hp8 Hpe Happ (_ & _ & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists (Z_to_bv 8 0). split; [|left; reflexivity].
  assert (Hsh : shadow_addr (p + i) = shadow_addr p + i / 8)
    by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  rewrite Hsh.
  assert (Hq : 0 <= i / 8 < Z.of_nat z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk : (Z.to_nat (i / 8) < z)%nat) by lia.
  pose proof (Hb (Z.to_nat (i / 8))) as E. rewrite repeat_length in E. specialize (E Hk).
  rewrite Z2Nat.id in E by lia. rewrite E. apply r1_nth_repeat. exact Hk.
Qed.

Lemma r1_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

(* ---- branch and store-end helpers ---- *)

Ltac r1_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first
        [ replace c with true;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?lib.Lib.MState.unsigned_lit by lia; solve_cond]
        | replace c with false;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?lib.Lib.MState.unsigned_lit by lia; solve_cond] ]
  end.

(* The end of a turn: the byte v stored at d, nothing else written. *)
Ltac r1_post v :=
  lazymatch goal with
  | |- munch _ ?m (write_to_mem ?m _ ?BS) /\ _ =>
      let EBS := fresh "EBS" in
      assert (EBS : BS = [v])
        by (first [apply le1_zxb | (apply r1_le1_lit; lia) | (vm_compute; reflexivity) | reflexivity]);
      rewrite EBS;
      split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|];
      split; [apply wmono_write, wmono_refl|];
      apply bytes_at_write_same; cbn [length]; lia
  end.

Lemma r1_land1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

(* zero path of turn t: 0x81414 (s9 = 0) -> store our[t] = 0 -> 0x81414 (t+1) or 0x81b14 *)
Lemma r1_z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d K l r : Z) (kb : byte),
    a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 l -> a3 = Z_to_bv 64 7 -> a4 = Z_to_bv 64 d ->
    s9 = Z_to_bv 64 0 -> s10 = Z_to_bv 64 K ->
    0 <= d -> d + 1 < 2 ^ 64 -> 1 <= l <= 6 -> 0 <= K -> d / 8 + K + 1 < 2 ^ 64 ->
    0 <= r < 8 -> d mod 8 = r ->
    ov_read_bytes rsegs m (wa (d / 8 + K)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ r < bv_signed kb) ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (d + 1)) (Z_to_bv 64 (l + 1)) a2 a3
                       (Z_to_bv 64 (d + 1)) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if l =? 6 then 0x81b14 else 0x81414)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m d K l r kb -> -> -> -> -> -> Hd0 Hd Hl HK Hsh Hr Hdr HR HOK HS.
  pose proof (rc_byte_signed kb) as KR.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  step. r1_br.
  step. rewrite (lib.Lib.MState.unsigned_lit d) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kb)) by lia.
  enough (KC : forall (x5 x6 : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 l) a2 (Z_to_bv 64 7)
                        (Z_to_bv 64 d) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x81428) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kb) 0) as [E|E]; cbn [negb]; [apply KC|].
    step. rewrite (lib.Lib.MState.unsigned_lit d) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (d mod 8) (bv_signed kb)) by lia.
    replace (d mod 8 <? bv_signed kb) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC. }
  intros x5 x6.
  step. step. step. step. step. step.
  destruct (Z.eq_dec l 6) as [E6|N6].
  - subst l. r1_br. step.
    apply evt_done. unfold Q. do 3 eexists. split; [reflexivity|]. r1_post (Z_to_bv 8 0).
  - r1_br.
    apply evt_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq l 6) N6).
    do 3 eexists. split; [reflexivity|]. r1_post (Z_to_bv 8 0).
Qed.

(* consume path of turn t: 0x81414 (s9 = v >= 1) -> our[t] = in-byte b -> 0x81414 (t+1) or 0x814a4 (t = 5) *)
Lemma r1_ld_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ou t K A q v : Z) (b kq kd : byte),
    a0 = Z_to_bv 64 (ou + t) -> a1 = Z_to_bv 64 (t + 1) -> a2 = Z_to_bv 64 6 -> a4 = Z_to_bv 64 (ou + t) ->
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 v -> s10 = Z_to_bv 64 K ->
    0 <= t <= 5 -> 0 <= ou -> ou + 8 < 2 ^ 64 -> ou mod 8 = 0 ->
    0 < q -> q + 1 < 2 ^ 64 -> 1 <= v -> v + 2 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 -> (ou + t) / 8 + K + 1 < 2 ^ 64 ->
    0 <= A -> A + 176 <= 2 ^ 64 -> ou + 8 <= A ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa ((ou + t) / 8 + K)) 1 = Some [kd] ->
    (bv_signed kd = 0 \/ t < bv_signed kd) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 ou)) ->
    store_ok rsegs m (wa (ou + t)) 1 = true ->
    evt rsegs
      (fun ms' => exists (x5 x6 x7 : word) (m' : word -> option byte),
         ms' = (if t =? 5
                then MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1)) a2 a3
                             (Z_to_bv 64 ou) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 q) (Z_to_bv 64 (q + 1))
                             (Z_to_bv 64 (v - 1)) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x814a4) fc None m' (seg_rom rsegs)
                else MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ou + t + 1)) (Z_to_bv 64 (t + 2)) a2 a3
                             (Z_to_bv 64 (ou + t + 1)) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (q + 1))
                             (Z_to_bv 64 (q + 1)) (Z_to_bv 64 (v - 1)) (Z_to_bv 64 (v - 1)) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x81414) fc None m' (seg_rom rsegs)) /\
         munch [(ou + t, ou + t + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (ou + t) [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ou t K A q v b kq kd -> -> -> -> -> -> -> -> Ht Hou0 Hou Hou8 Hq0 Hq Hv0 Hv HK Hshq Hshd
    HA0 HA HAo HRq HOKq HRd HOKd HRb HSP HS.
  pose proof (rc_byte_signed kq) as KRq. pose proof (rc_byte_signed kd) as KRd.
  assert (Hdm : (ou + t) mod 8 = t) by (Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  step. r1_br.
  step. rewrite (lib.Lib.MState.unsigned_lit q) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kq)) by lia.
  enough (KC1 : forall (x5 x6 : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1))
                         (Z_to_bv 64 6) a3 (Z_to_bv 64 (ou + t)) x5 x6 a7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
                         (Z_to_bv 64 v) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x81460) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kq) 0) as [E|E]; cbn [negb]; [apply KC1|].
    step. rewrite (lib.Lib.MState.unsigned_lit q) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (q mod 8) (bv_signed kq)) by lia.
    replace (q mod 8 <? bv_signed kq) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC1. }
  intros x5 x6.
  step. rewrite (lib.Lib.MState.unsigned_lit (ou + t)) by lia. rewrite rc_shr3.
  step. step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kd)) by lia.
  enough (KC2 : forall (y6 y7 : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1))
                         (Z_to_bv 64 6) a3 (Z_to_bv 64 (ou + t)) (zxb b) y6 y7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
                         (Z_to_bv 64 v) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x81474) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kd) 0) as [E|E]; cbn [negb]; [apply KC2|].
    step. rewrite (lib.Lib.MState.unsigned_lit (ou + t)) by lia. rewrite rc_land7. rewrite Hdm.
    step.
    rewrite (rc_lts_signed t (bv_signed kd)) by lia.
    replace (t <? bv_signed kd) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC2. }
  intros y6 y7.
  step. step. step.
  rewrite le1_zxb.
  assert (HL : ov_read_bytes rsegs (write_to_mem m (Z_to_bv 64 (ou + t)) [b]) (wa (A + 168)) 8
               = Some (le8 (Z_to_bv 64 ou))).
  { assert (HB' : bytes_at rsegs (write_to_mem m (Z_to_bv 64 (ou + t)) [b]) (A + 168) (le8 (Z_to_bv 64 ou)))
      by (apply bytes_at_write_other;
          [exact HSP | lia | cbn [length]; lia | rewrite length_le8; cbn [length]; lia]).
    pose proof (bytes_at_ov_read rsegs _ _ _ 0 8 HB' ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r in HH. rewrite HH. f_equal. }
  step. step.
  destruct (Z.eq_dec t 5) as [E5|N5].
  - subst t. r1_br.
    apply evt_done. unfold Q. cbv beta.
    do 4 eexists. split; [cbn [Z.eqb]; reflexivity|].
    split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|].
    split; [apply wmono_write, wmono_refl|].
    apply bytes_at_write_same; cbn [length]; lia.
  - r1_br.
    step. step. step. step. step. step.
    apply evt_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq t 5) N5).
    replace (Z_to_bv 64 (ou + (t + 1))) with (Z_to_bv 64 (ou + t + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (t + 1 + 1)) with (Z_to_bv 64 (t + 2)) by (f_equal; lia).
    replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
    do 4 eexists. split; [reflexivity|].
    split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|].
    split; [apply wmono_write, wmono_refl|].
    apply bytes_at_write_same; cbn [length]; lia.
Qed.

(* The mode read, 0x814a4 -> 0x81b14 (left = 0 at 0x81984, or the even-mode arm) or 0x814d0 (odd mode).  On the
   0x81b14 arms the cursor s6 and left s9 are exposed: w = 0 (0x81984 `li s9,0; mv s6,s7`): s6 = pm, s9 = 0;
   even mode (0x814c0 `addi s9,s9,-2`, 0x814c8 `addi s6,s6,2`): s6 = pm + 1, s9 = w - 1. *)
Lemma r1_mode_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pm w K : Z) (bm km : byte),
    s6 = Z_to_bv 64 (pm - 1) -> s7 = Z_to_bv 64 pm -> s8 = Z_to_bv 64 w -> s9 = Z_to_bv 64 (w + 1) ->
    s10 = Z_to_bv 64 K ->
    0 < pm -> pm + 2 < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> pm / 8 + K + 1 < 2 ^ 64 ->
    (w <> 0 -> ov_read_bytes rsegs m (wa (pm / 8 + K)) 1 = Some [km]) ->
    (w <> 0 -> bv_signed km = 0 \/ pm mod 8 < bv_signed km) ->
    (w <> 0 -> ov_read_bytes rsegs m (wa pm) 1 = Some [bm]) ->
    evt rsegs
      (fun ms' =>
         (exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 22 = Z_to_bv 64 (if w =? 0 then pm else pm + 1) /\
            getr R 25 = Z_to_bv 64 (if w =? 0 then 0 else w - 1)) \/
         (bv_unsigned bm mod 2 = 1 /\ 1 <= w /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                          (Z_to_bv 64 (pm + 1)) (zxb bm) (Z_to_bv 64 w) (Z_to_bv 64 (w - 1)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pm w K bm km -> -> -> -> -> Hpm0 Hpm Hw0 Hw HK Hshm HRk HOKk HRm.
  pose proof (rc_byte_signed km) as KRk.
  pose proof (bv_unsigned_in_range 8 bm) as HBM. unfold bv_modulus in HBM. cbn in HBM.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  step.
  destruct (Z.eq_dec w 0) as [E0|N0].
  - subst w. r1_br.
    step. step. step.
    apply evt_done. unfold Q. cbv beta. left. eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; reflexivity.
  - r1_br.
    specialize (HRk N0). specialize (HOKk N0). specialize (HRm N0).
    step. rewrite (lib.Lib.MState.unsigned_lit pm) by lia. rewrite rc_shr3.
    step. step. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed km)) by lia.
    enough (KC : forall (x0 x1 : word),
      evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                           (Z_to_bv 64 (pm - 1)) (Z_to_bv 64 pm) (Z_to_bv 64 w) (Z_to_bv 64 (w + 1))
                           (Z_to_bv 64 K) s11
                           t3 t4 t5 t6)
                      F (Z_to_bv 64 0x814bc) fc None m (seg_rom rsegs))).
    { destruct (Z.eqb_spec (bv_signed km) 0) as [E|E]; cbn [negb]; [apply KC|].
      step. step. rewrite (lib.Lib.MState.unsigned_lit pm) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed (pm mod 8) (bv_signed km)) by lia.
      replace (pm mod 8 <? bv_signed km) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. step. apply KC. }
    intros x0 x1.
    step. step. step.
    unfold zxb. rewrite (lib.Lib.MState.unsigned_lit (bv_unsigned bm)) by lia. rewrite r1_land1 by lia.
    step. step.
    destruct (Z.eq_dec (bv_unsigned bm mod 2) 0) as [Ev|Od].
    + rewrite Ev. r1_br.
      replace (Z_to_bv 64 (pm - 1 + 2)) with (Z_to_bv 64 (pm + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (w + 1 + -2)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
      apply evt_done. unfold Q. cbv beta. left. eexists.
      rewrite (proj2 (Z.eqb_neq w 0) N0).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    + r1_br.
      apply evt_done. unfold Q. cbv beta. right.
      split; [lia|]. split; [lia|].
      replace (Z_to_bv 64 (pm - 1 + 2)) with (Z_to_bv 64 (pm + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (w + 1 + -2)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
      do 2 eexists. reflexivity.
Qed.


(* The odd-mode tail is run in three stages, one per kind of write: the six spill stores into [A + 48, A + 136)
   (real-stack bytes), the count cell's shadow byte S(fr) + 332 = 00 (a frame-shadow byte), and the count cell
   with the catalogue call (frame body and the callee window).  The slot's FRA is rebuilt stage by stage at the
   cut level (sl_fr_cl for the two app stages, sl_fr_meta for the shadow one), which is why the stages are kept
   apart here. *)

(* 0x814d0 .. 0x814e4: ra, t6, t5, t4, t3, t2 to [A + 72], [A + 80], [A + 88], [A + 56], [A + 48], [A + 128].  The
   write set is stated store by store ([A + 48, A + 64), [A + 72, A + 96), [A + 128, A + 136)), so the PRO spill
   [A + 120] in the gap is seen to survive. *)
Lemma r1_spill_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (x48 x56 x72 x80 x88 x128 sh1 cs : list byte),
    s1 = Z_to_bv 64 A -> ra0 = Z_to_bv 64 (fr + 2496) -> t2 = Z_to_bv 64 (fr + 544) ->
    t3 = Z_to_bv 64 (fr + 2256) -> t4 = Z_to_bv 64 (fr + 2368) -> t5 = Z_to_bv 64 (fr + 2448) ->
    t6 = Z_to_bv 64 (fr + 2464) ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (A + 48) [CB 8 x48] -> rw_cells rsegs m (A + 56) [CB 8 x56] ->
    rw_cells rsegs m (A + 72) [CB 8 x72] -> rw_cells rsegs m (A + 80) [CB 8 x80] ->
    rw_cells rsegs m (A + 88) [CB 8 x88] -> rw_cells rsegs m (A + 128) [CB 8 x128] ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814e8) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\ shadow_rw m' /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (Sh + 332) [CB 1 sh1] /\ rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))) /\
         bytes_at rsegs m' (A + 56) (le8 (Z_to_bv 64 (fr + 2368))) /\
         bytes_at rsegs m' (A + 72) (le8 (Z_to_bv 64 (fr + 2496))) /\
         bytes_at rsegs m' (A + 80) (le8 (Z_to_bv 64 (fr + 2464))) /\
         bytes_at rsegs m' (A + 88) (le8 (Z_to_bv 64 (fr + 2448))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)).
Proof.
 
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv x48 x56 x72 x80 x88 x128 sh1 cs -> -> -> -> -> -> ->
    Hfr0 HfrA HspA HA64 HShlo HShA HAapp CH48 CH56 CH72 CH80 CH88 CH128 CHsh CHc STA ST HAC HSW.
  pose proof (munch_refl [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (Hsho : forall a, in_shadow a -> ~ (A + 48 <= a < A + 136)).
  { intros a Ha Hin. exact (app_not_shadow a (HAapp a ltac:(lia)) Ha). }
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split.
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  split.
  { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha. left. pose proof (Hsho a Ha).
    cbn [outside]. repeat split; first [exact I | lia]. }
  split; [exact STA|]. split; [exact ST|].
  split; [exact CHsh|]. split; [exact CHc|].
  split.
  { destruct CH48 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH128 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH56 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH72 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH80 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  { destruct CH88 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
Qed.

(* 0x814e8: `sb zero,332(s3)` marks the catalogue count cell's granule usable. *)
Lemma r1_shadow_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (sh1 cs : list byte),
    s3 = Z_to_bv 64 Sh ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    Sh + 392 <= spv - 16 -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814ec) fc None m' (seg_rom rsegs) /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\ shadow_rw m' /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814e8) fc None m (seg_rom rsegs)).
Proof.
 
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv sh1 cs -> Hfr0 HfrA HspA HA64 HShlo HShA HShsp HShD HAapp Hwapp
    CHsh CHc STA ST HAC HSW H48b H128b.
  pose proof (munch_refl [(Sh + 332, Sh + 333)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HShD as [HShD|HShD].
  { r1_sb.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (HSHb : bytes_at rsegs m1 (Sh + 332) [Z_to_bv 8 0]).
    { destruct CHsh as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    apply evt_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split.
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    split.
    { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha.
      destruct (Z_le_gt_dec (Sh + 332) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 333)) as [H2|H2]|].
      - right. apply (r1_ba_rd m1 (Sh + 332) [Z_to_bv 8 0] a HSHb). cbn [length]. lia.
      - left. cbn [outside]. split; [lia | exact I].
      - left. cbn [outside]. split; [lia | exact I]. }
    split; [exact STA|]. split; [exact ST|]. split; [exact CHc|]. split; [exact HSHb|].
    split; [exact H48b | exact H128b]. }
  { r1_sb.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (HSHb : bytes_at rsegs m1 (Sh + 332) [Z_to_bv 8 0]).
    { destruct CHsh as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    apply evt_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split.
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    split.
    { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha.
      destruct (Z_le_gt_dec (Sh + 332) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 333)) as [H2|H2]|].
      - right. apply (r1_ba_rd m1 (Sh + 332) [Z_to_bv 8 0] a HSHb). cbn [length]. lia.
      - left. cbn [outside]. split; [lia | exact I].
      - left. cbn [outside]. split; [lia | exact I]. }
    split; [exact STA|]. split; [exact ST|]. split; [exact CHc|]. split; [exact HSHb|].
    split; [exact H48b | exact H128b]. }
Qed.

(* 0x814ec .. 0x814f4: the count cell is zeroed, a0 takes it, and reac_box_catalogue runs by its contract. *)
Lemma r1_call_evt : RBC.reac_box_catalogue_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr Sh spv : Z) (cs : list byte),
    sp = Z_to_bv 64 spv -> s2 = Z_to_bv 64 (fr + 2656) ->
    6283264 <= fr -> fr + 3136 <= 140737488355328 -> fr mod 8 = 0 -> fr + 3136 <= A -> spv <= A ->
    A + 416 <= 2 ^ 64 -> 6283264 <= spv - 16 -> spv <= 140737488355328 ->
    (fr + 2664 <= spv - 16 \/ spv <= fr) -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    shadow_addr (fr + 2656) = Sh + 332 ->
    (forall a, fr <= a < fr + 3136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (fr + 2656) [CB 8 cs] -> bytes_at rsegs m (Sh + 332) [Z_to_bv 8 0] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x814f8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 0x9e800 /\
         munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         shadow_rw m' /\ stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' (fr + 2656) (le8 (Z_to_bv 64 11)) /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814ec) fc None m (seg_rom rsegs)).
Proof.
 
  intros CATC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv cs -> -> HfrGT HfrE Hfr8 HfrA HspA HA64 HspGT HspE Hsep HShD Hshc Happ Hwapp HAapp
    CHc HSHb STA ST HAC HSW H48b H128b.
  unfold RBC.reac_box_catalogue_contract, RBC.REAC_BOX_CATALOGUE, RBC.REAC_BOX_CATALOGUE_FRAME,
    RBC.BOX_CATALOGUE in CATC.
  pose proof (munch_refl [(fr + 2656, fr + 2664); (spv - 16, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HShD as [HShD|HShD].
  {
    step. step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (Hsho : forall a, in_shadow a -> ~ (fr + 2656 <= a < fr + 2664) /\ ~ (spv - 16 <= a < spv)).
    { intros a Ha. split; intros Hin.
      - exact (app_not_shadow a (Happ a ltac:(lia)) Ha).
      - exact (app_not_shadow a (Hwapp a ltac:(lia)) Ha). }
    assert (HAC1 : asan_cells m1).
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (HADc : addressable m1 (fr + 2656) 8).
    { apply (r1_addr_z m1 (fr + 2656) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia
        | unfold APPMEM_END; lia | intros i Hi; apply Happ; lia |].
      rewrite Hshc. cbn [repeat]. exact HSHb. }
    assert (HWRc : wr_at rsegs m1 (fr + 2656) 8).
    { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add] in Hw. exact Hw. }
    eapply evt_cut.
    { eapply CATC with (c := fr + 2656) (lo := spv - 16).
      - reflexivity.
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia. exact ST.
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia. lia.
      - exact HAC1.
      - exact HSW1.
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia.
        intros x [Hx | [Hx | Hx]].
        + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
        + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
        + destruct (Hsho x Hx) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia).
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia.
        right. split; [Z.div_mod_to_equations; lia|]. split; [exact HWRc|].
        split; [lia | exact HADc]. }
    intros ms' PO.
    destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
    subst ms'.
    rewrite (lib.Lib.MState.unsigned_lit spv) in MU2, ST2 by lia.
    replace (fr + 2656 + 8) with (fr + 2664) in MU2 by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2656) 0) ltac:(lia)) in HZ.
    replace (ret_pc (Z_to_bv 64 0x814f8)) with (Z_to_bv 64 0x814f8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MUf : munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m').
    { apply (munch_trans _ m m1 m'); [exact MU|].
      apply (munch_weaken [(spv - 16, spv); (fr + 2656, fr + 2664)]);
        [intros x Hx; cbn [outside] in Hx |- *; clear - Hx; tauto | exact MU2]. }
    assert (HSW2 : shadow_rw m').
    { apply (r1_shadow_rw _ m1 m' HSW1 MU2 WM2). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (STA2 : stk rsegs m' (A + 48) (A + 136)).
    { apply (r1_stk_tr _ m1 m' _ _ STA MU2 WM2). intros x Hx. left.
      cbn [outside]. repeat split; (exact I || lia). }
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
    split; [exact HSW2|]. split; [exact STA2|]. split; [exact ST2|].
    split; [exact HZ|].
    split.
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H48b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H128b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
  }
  {
    step. step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (Hsho : forall a, in_shadow a -> ~ (fr + 2656 <= a < fr + 2664) /\ ~ (spv - 16 <= a < spv)).
    { intros a Ha. split; intros Hin.
      - exact (app_not_shadow a (Happ a ltac:(lia)) Ha).
      - exact (app_not_shadow a (Hwapp a ltac:(lia)) Ha). }
    assert (HAC1 : asan_cells m1).
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (HADc : addressable m1 (fr + 2656) 8).
    { apply (r1_addr_z m1 (fr + 2656) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia
        | unfold APPMEM_END; lia | intros i Hi; apply Happ; lia |].
      rewrite Hshc. cbn [repeat]. exact HSHb. }
    assert (HWRc : wr_at rsegs m1 (fr + 2656) 8).
    { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add] in Hw. exact Hw. }
    eapply evt_cut.
    { eapply CATC with (c := fr + 2656) (lo := spv - 16).
      - reflexivity.
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia. exact ST.
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia. lia.
      - exact HAC1.
      - exact HSW1.
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia.
        intros x [Hx | [Hx | Hx]].
        + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
        + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
        + destruct (Hsho x Hx) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia).
      - rewrite (lib.Lib.MState.unsigned_lit spv) by lia.
        right. split; [Z.div_mod_to_equations; lia|]. split; [exact HWRc|].
        split; [lia | exact HADc]. }
    intros ms' PO.
    destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
    subst ms'.
    rewrite (lib.Lib.MState.unsigned_lit spv) in MU2, ST2 by lia.
    replace (fr + 2656 + 8) with (fr + 2664) in MU2 by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2656) 0) ltac:(lia)) in HZ.
    replace (ret_pc (Z_to_bv 64 0x814f8)) with (Z_to_bv 64 0x814f8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MUf : munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m').
    { apply (munch_trans _ m m1 m'); [exact MU|].
      apply (munch_weaken [(spv - 16, spv); (fr + 2656, fr + 2664)]);
        [intros x Hx; cbn [outside] in Hx |- *; clear - Hx; tauto | exact MU2]. }
    assert (HSW2 : shadow_rw m').
    { apply (r1_shadow_rw _ m1 m' HSW1 MU2 WM2). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (STA2 : stk rsegs m' (A + 48) (A + 136)).
    { apply (r1_stk_tr _ m1 m' _ _ STA MU2 WM2). intros x Hx. left.
      cbn [outside]. repeat split; (exact I || lia). }
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
    split; [exact HSW2|]. split; [exact STA2|]. split; [exact ST2|].
    split; [exact HZ|].
    split.
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H48b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H128b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
  }
Qed.

(* ---- seg_R1 on the official cuts (SlotInv.v push 13: Inv_A81414_at -> Inv_A814f8 / Inv_A81b14).  Each turn and
   the tail are one sl_run_lib run (Seg/Tac_b5.v) feeding the evt lemmas above; FRA is carried across the run's
   write set by r1_fra_app (the canonical sl_fr_cl, the write set classified into the frame body, the callee
   window and the spill cells [A + 48, A + 136); FSREC by fra_fsrec_stklo) and r1_fra_sh (the canonical
   sl_fr_meta for the count cell's shadow byte), the heap invariant by a_laws_store (real arm: every written
   byte is a_store_ok) or Tac_fs.a_fs_ok_store_AH (side arm), ENT by ent_store / ent_mat, and the model by
   sl_fra_move.  No mem_inv anywhere (push 5b): the one callee, reac_box_catalogue, has no mem_inv premise.
   PRO (push 13B) is carried by Seg/RcPro.v's rc_pro_keep: every written byte is the frame body, its shadow or at
   or above sp - FN_STACK, hence rc_away (r1_away).  The loop is closed by well-founded induction on 5 - t. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 RcPro.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

(* firstn of OUR grows by one model byte per turn. *)
Lemma r1_our_step : forall inp t, (t < 6)%nat ->
  firstn (S t) (OUR inp) = firstn t (OUR inp) ++ [RcIdentModel.nthb inp t].
Proof.
  intros inp t Ht. unfold OUR. cbn [seq map].
  do 6 (destruct t as [|t]; [reflexivity|]). lia.
Qed.

Lemma r1_nth_past : forall inp t, (length inp <= t)%nat -> RcIdentModel.nthb inp t = Z_to_bv 8 0.
Proof. intros inp t H. unfold RcIdentModel.nthb, RcIdentModel.zb. apply nth_overflow. exact H. Qed.

Lemma r1_nth_OUR : forall inp t, (t < 6)%nat -> nth_error (OUR inp) t = Some (RcIdentModel.nthb inp t).
Proof.
  intros inp t Ht. unfold OUR. cbn [seq map].
  do 6 (destruct t as [|t]; [reflexivity|]). lia.
Qed.

(* A one-byte read of a known byte list. *)
Lemma r1_rd_at : forall m a bs i (b : byte), bytes_at rsegs m a bs -> 0 <= i ->
  nth_error bs (Z.to_nat i) = Some b -> ov_read_bytes rsegs m (wa (a + i)) 1 = Some [b].
Proof.
  intros m a bs i b H Hi Hn.
  assert (Hlt : (Z.to_nat i < length bs)%nat) by (apply nth_error_Some; intros E; rewrite E in Hn; discriminate).
  pose proof (bytes_at_ov_read rsegs m a bs (Z.to_nat i) 1 H ltac:(lia)) as HH.
  rewrite Z2Nat.id in HH by lia. rewrite HH. f_equal.
  assert (Hb : nth_error (skipn (Z.to_nat i) bs) 0 = Some b)
    by (rewrite nth_error_skipn, Nat.add_0_r; exact Hn).
  destruct (skipn (Z.to_nat i) bs) as [|b' rest]; cbn in Hb; [discriminate|].
  injection Hb as <-. reflexivity.
Qed.

Lemma r1_rd1 : forall m a (b : byte), bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. pose proof (r1_rd_at m a [b] 0 b H ltac:(lia) ltac:(reflexivity)) as HH.
  rewrite Z.add_0_r in HH. exact HH.
Qed.

(* Every image byte is below GT: the segments of the image all end there. *)
Lemma r1_segs_lo : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < 6283264.
Proof.
  intros x seg H.
  assert (HB : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB.
  destruct (KindBGlue.kb_find_segment rsegs x 1 seg H) as (Hin & Hlo & Hhi).
  pose proof (HB seg Hin) as Hb. apply Z.leb_le in Hb.
  pose proof (N2Z.is_nonneg (seg_base seg)). lia.
Qed.

(* ro_agree across a run that writes no image byte. *)
Lemma r1_ro_keep : forall (W : list LF.ivl) m m', ro_agree rsegs m -> LF.munch W m m' ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) -> ro_agree rsegs m'.
Proof.
  intros W m m' HRO MU HW a Hro.
  unfold mrd. rewrite (MU a); [exact (HRO a Hro)|].
  unfold ro_addr in Hro. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
  apply HW. exact (r1_segs_lo _ s E).
Qed.

(* A shadow byte is never application memory. *)
Lemma r1_sh_app_dj : forall x a, in_shadow x -> app_mem a -> x + 1 <= a \/ a + 1 <= x.
Proof.
  intros x a Hx Ha.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha.
  destruct Hx as [Hx|Hx]; destruct Ha as [Ha|Ha]; lia.
Qed.

Lemma r1_addr_sub : forall m p n i, addressable m p n -> 0 <= i -> i + 1 <= n -> addressable m (p + i) 1.
Proof.
  intros m p n i (H1 & H2 & H3 & H) Hi Hin. split; [lia|]. split; [lia|]. split; [lia|].
  intros k Hk. replace (p + i + k) with (p + (i + k)) by lia. apply H. lia.
Qed.

(* our[] after one turn: the byte v landed at our + t, the rest of the six bytes kept. *)
Lemma r1_our_keep : forall m m' ou t (pre junk : list byte) (v : byte),
  bytes_at rsegs m ou (pre ++ junk) -> length pre = Z.to_nat t -> 0 <= t -> (1 <= length junk)%nat ->
  LF.munch [(ou + t, ou + t + 1)] m m' -> bytes_at rsegs m' (ou + t) [v] ->
  bytes_at rsegs m' ou ((pre ++ [v]) ++ tl junk).
Proof.
  intros m m' ou t pre junk v H Hp Ht Hj MU HV.
  pose proof H as Hb. apply bytes_at_bound in Hb. rewrite length_app in Hb.
  apply bytes_at_app in H. destruct H as (H1 & H2).
  rewrite Hp, Z2Nat.id in H2 by lia.
  destruct junk as [|b0 junk']; [cbn in Hj; lia|].
  change (b0 :: junk') with ([b0] ++ junk') in H2.
  apply bytes_at_app in H2. destruct H2 as (H2a & H2b). cbn [length Z.of_nat] in H2b.
  apply bytes_at_app. split.
  - apply bytes_at_app. split.
    + apply (bytes_at_transport rsegs [(ou + t, ou + t + 1)] m m' ou pre H1 MU).
      rewrite Hp, Z2Nat.id by lia. cbn [disjoint_from]. split; [left; lia | exact I].
    + rewrite Hp, Z2Nat.id by lia. exact HV.
  - rewrite length_app. cbn [length]. rewrite Hp.
    replace (ou + Z.of_nat (Z.to_nat t + 1)) with (ou + t + 1) by lia.
    apply (bytes_at_transport rsegs [(ou + t, ou + t + 1)] m m' (ou + t + 1) junk' H2b MU).
    cbn [disjoint_from]. split; [right; lia | exact I].
Qed.

(* A frame-shadow byte is in the shadow map. *)
Lemma r1_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW ->
  in_shadow (Sfr fr + k).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros fr k Happ Hk. replace (Sfr fr + k) with (shadow_addr (fr + 8 * k)).
  - apply shadow_of_app. apply Happ. lia.
  - rewrite r1_sh8. unfold Sfr. reflexivity.
Qed.

(* The instrumented globals of the image lie in [0x21140, 0x9f8e8). *)
Lemma r1_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AFw.frame_AG in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* An 8-byte cell of a stack window. *)
Lemma r1_cell8 : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists xs, rw_cells rsegs m a [CB 8 xs].
Proof.
  intros m lo hi a H Hlo Hhi.
  destruct (stk_split rsegs m lo a hi H ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs m a (a + 8) hi H1 ltac:(lia)) as (H2 & _).
  destruct (stk_bytes rsegs m a (a + 8) H2 ltac:(lia)) as (xs & Hl & Hb).
  exists xs. replace 8%nat with (length xs) by lia. apply r1_rw_CB; [exact Hb|].
  replace (Z.of_nat (length xs)) with (a + 8 - a) by lia. exact (r1_wr_stk _ _ _ H2).
Qed.

Lemma r1_cell1 : forall m a, stk rsegs m a (a + 1) -> exists xs, rw_cells rsegs m a [CB 1 xs].
Proof.
  intros m a H.
  destruct (stk_bytes rsegs m a (a + 1) H ltac:(lia)) as (xs & Hl & Hb).
  exists xs. replace 1%nat with (length xs) by lia. apply r1_rw_CB; [exact Hb|].
  replace (Z.of_nat (length xs)) with (a + 1 - a) by lia. exact (r1_wr_stk _ _ _ H).
Qed.

(* An 8-byte cell of a stack window, as a C8 cell of the state after a run that missed it. *)
Lemma r1_c8 : forall (W : list LF.ivl) m m' a (v : word) lo hi,
  bytes_at rsegs m a (le8 v) -> stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  LF.munch W m m' -> LF.wmono rsegs m m' -> LF.disjoint_from W a 8 ->
  rw_cells rsegs m' a [C8 v].
Proof.
  intros W m m' a v lo hi Hb Hs Hlo Hhi MU WM HD.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply (bytes_at_transport rsegs W m m' a _ Hb MU). rewrite length_le8. exact HD.
  - replace (Z.of_nat (cells_size [C8 v])) with 8 by reflexivity.
    apply (LF.wr_at_transport rsegs m m' a 8); [|exact WM].
    pose proof (r1_wr_stk m lo hi Hs) as Hw.
    replace a with (lo + (a - lo)) by lia.
    apply (wr_at_sub m lo (hi - lo) (a - lo) 8 Hw); lia.
Qed.

(* The FakeStack's metadata is its first 36864 bytes. *)
Lemma r1_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

Section R1.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.reac_box_catalogue_contract.

(* The heap invariant, the ownership relation and the real stack's bounds across a run that writes only the frame
   body, the frame's shadow and real-stack bytes at or above stklo: the real-stack arm by a_laws_store (every
   written byte is a_store_ok), the side-stack arm by Tac_fs.a_fs_ok_store_AH (the frame and its shadow are the
   FakeStack's, the rest is a_store_ok). *)
Lemma r1_ah : forall g fr regs mem mem' md (W : list LF.ivl),
  FRA B APIf ra g fr [] regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' ->
  (forall x, ~ LF.outside W x -> (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)) ->
  (forall x, ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
  (forall a, ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
             ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md =
    ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md =
    ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr regs mem mem' md W HFRA MU WM HWcl HRD.
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
    by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
  assert (Hsh8 : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> 8 * (x - Sfr fr) + fr = 8 * (x - Sfr fr) + fr /\
                   shadow_addr (fr + 8 * (x - Sfr fr)) = x).
  { intros x Hx. split; [reflexivity|]. rewrite r1_sh8. unfold Sfr. lia. }
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs _]]]].
  - assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok.
      destruct (r1_out_dec W x) as [Ho|Hno].
      - apply MU. rewrite A.Tk.UL.MState.unsigned_lit by exact Hx. exact Ho.
      - exfalso. apply Hnok. destruct (HWcl x Hno) as [H|[H|H]].
        + right; left. pose proof (Hreal x ltac:(lia)). lia.
        + right; right; right. exists (fr + 8 * (x - Sfr fr)).
          split; [symmetry; exact (proj2 (Hsh8 x H))|].
          right; left. apply Hreal.
          assert (Hd : 0 <= x - Sfr fr < FRAME_SHADOW) by lia. lia.
        + right; left. exact H. }
    destruct (ACw.a_laws_store _ _ _ _ _ ALAWS ([] ++ g_H g) mem mem' md HAH Hmc Hwrit)
      as (HAH' & Hown & Hstk' & Hhi').
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact Hstk' | exact Hhi'].
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
    pose proof (Hfsb FS HwFS HFSr) as HFSfr.
    destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FS HAH HwFS HFSr)
      as (HGTFS & HFSend & _ & HFSapp).
    assert (HFS64 : FS + ACw.FS_SIZE <= 2 ^ 64).
    { pose proof (HFSapp (FS + ACw.FS_SIZE - 1) ltac:(unfold ACw.FS_SIZE in *; lia)) as H.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (b & Hb).
      destruct (r1_out_dec W q) as [Ho|Hno].
      - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
        rewrite A.Tk.UL.MState.unsigned_lit by exact Hq. exact Ho.
      - destruct (HRD q Hno) as (b' & Hb'). exists b'. exact Hb'. }
    assert (Hmeta : forall q, fs_meta FS q -> LF.outside W q).
    { intros q Hq. pose proof (r1_fs_meta_range FS q Hq) as Hqr.
      assert (Hqa : app_mem q) by (apply HFSapp; unfold ACw.FS_SIZE in *; lia).
      destruct (r1_out_dec W q) as [Ho|Hno]; [exact Ho|].
      exfalso. destruct (HWcl q Hno) as [H|[H|H]].
      - lia.
      - pose proof (r1_sh_app_dj q q ltac:(rewrite <- (proj2 (Hsh8 q H));
          apply shadow_of_app; apply Happ'; lia) Hqa). lia.
      - unfold ACw.FS_SIZE in HFSend. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + ACw.FS_SIZE) ->
              ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ q = shadow_addr b) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh.
      destruct (r1_out_dec W q) as [Ho|Hno].
      - apply MU. rewrite A.Tk.UL.MState.unsigned_lit by exact Hq. exact Ho.
      - exfalso. destruct (HWcl q Hno) as [H|[H|H]].
        + apply Hnfs. unfold ACw.FS_SIZE in *. lia.
        + apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
          split; [unfold ACw.FS_SIZE in *; lia | symmetry; exact (proj2 (Hsh8 q H))].
        + apply Hnok. right; left. exact H. }
    destruct (a_fs_ok_store_AH _ _ _ _ _ W ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU
                Hwrit Hpres Hmeta Hagree)
      as (HAH' & Hown & Hstk' & Hhi').
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact Hstk' | exact Hhi'].
Qed.

(* The slot's own frame geometry, as the FRA rebuilds want it: the frame is application memory above GT, the
   frame shadow is in the shadow map, and sp (hence the spill base A) is high above the image. *)
Lemma r1_geom : forall g fr regs mem md,
  FRA B APIf ra g fr [] regs mem md ->
  ACw.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
  fr + FRAME_BYTES <= bv_unsigned (getr regs 9) /\ bv_unsigned (getr regs 9) + 416 <= g_S g /\
  ACw.aspZ regs <= bv_unsigned (getr regs 9) /\
  17592186044416 + 2147450880 + 1040384 <= ACw.aspZ regs /\
  g_S g < APPMEM_END /\
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md <= ACw.aspZ regs - 4096 /\
  17592186044416 + 2147450880 + 1048576 <= g_S g /\
  2147450880 <= Sfr fr.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr regs mem md HFRA.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))
                ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); unfold AFw.SLOT_STACK in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply A.Tk.UL.MState.unsigned_lit; exact HA64).
  unfold ACw.GT in HGT. unfold HIGHMEM_BEG in Hhigh. unfold AFw.SLOT_STACK in Hstklo.
  rewrite HbvA, Haspz.
  split; [unfold ACw.GT; lia|]. split; [exact Happ|]. split; [exact Hfa|]. split; [exact HA416|].
  split; [exact Hspa|]. split; [lia|]. split; [exact HAPP|]. split; [lia|]. split; [lia|].
  unfold Sfr, shadow_addr, ASAN_K.
  assert (Hfr0 : 0 <= fr) by (unfold ACw.GT in HGT; lia).
  Z.div_mod_to_equations. lia.
Qed.

(* FRA across a stage whose write set is application memory inside the frame body, the spill cells
   [A + 48, A + 136) or the callee window [sp - 16, sp): the canonical sl_fr_cl. *)
Lemma r1_fra_app : forall g fr regs regs' mem mem' md (W : list LF.ivl),
  FRA B APIf ra g fr [] regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' ->
  AsanRTInv.rt_disjoint W -> all_app W ->
  (forall x, ~ LF.outside W x -> (fr + 24 <= x < fr + FRAME_BYTES) \/
     (bv_unsigned (getr regs 9) + 48 <= x < bv_unsigned (getr regs 9) + 136) \/
     (ACw.aspZ regs - 16 <= x < ACw.aspZ regs)) ->
  (forall x, ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr [] regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr regs regs' mem mem' md W HFRA MU WM HDJ HAW HWcl HRD E2 E3 E4 E8 E9 E19 E26.
  destruct (r1_geom g fr regs mem md HFRA) as (HGT & Happ & HfrA & HA416 & HspA & Hsplo & HSAPP & Hstklo4 & HSlo & HSfr).
  unfold ACw.GT in HGT.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); unfold AFw.SLOT_STACK in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply A.Tk.UL.MState.unsigned_lit; exact HA64).
  rewrite HbvA in HWcl, HfrA, HA416, HspA. rewrite Haspz in HWcl, HspA, Hsplo, Hstklo4.
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (Hplace 16 ltac:(unfold FN_STACK, AFw.SLOT_STACK; lia)) as Hsep. rewrite Haspz in Hsep.
  unfold APPMEM_END in HSAPP.
  (* the write set misses the image, the header, the spills, the saved registers and the frame shadow *)
  assert (Hout : forall x, 0 <= x < 6283264 -> LF.outside W x).
  { intros x Hx. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|[H|H]]; lia. }
  assert (Hnsh : forall x, (fr + 24 <= x < fr + FRAME_BYTES) \/ (A + 48 <= x < A + 136) \/ (sp - 16 <= x < sp) ->
            app_mem x).
  { intros x [H|[H|H]].
    - apply Happ. lia.
    - unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
    - unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
  assert (Hshout : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> LF.outside W x).
  { intros x Hx. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso.
    assert (Hin : in_shadow x) by (replace x with (Sfr fr + (x - Sfr fr)) by lia;
      apply r1_fsh; [exact Happ | lia]).
    pose proof (r1_sh_app_dj x x Hin (Hnsh x (HWcl x Hno))). lia. }
  destruct (r1_ah g fr regs mem mem' md W HFRA MU WM
              ltac:(intros x Hx; destruct (HWcl x Hx) as [H|[H|H]];
                    [left; lia | right; right; unfold APPMEM_END; lia
                     | right; right; unfold APPMEM_END; lia]) HRD)
    as (HAH' & Hown & HSTK' & HSTKhi').
  apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs' mem mem' md W HFRA MU WM
           (r1_ro_keep W mem mem' Hro MU Hout) HAW HDJ HAH' HSTK' Hout).
  - intros x Hx. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|[H|H]]; destruct Hsep as [Hs|Hs]; lia.
  - intros A0 HA0 HA0r x Hx.
    assert (A0 = A) by (rewrite <- HbvA, HA0, A.Tk.UL.MState.unsigned_lit by lia; reflexivity).
    subst A0. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|[H|H]]; destruct Hsep as [Hs|Hs]; lia.
  - intros x Hx. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|[H|H]]; destruct Hsep as [Hs|Hs]; lia.
  - exact Hshout.
  - intros A0 HA0 HA0r x Hx.
    assert (A0 = A) by (rewrite <- HbvA, HA0, A.Tk.UL.MState.unsigned_lit by lia; reflexivity).
    subst A0. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|[H|H]]; destruct Hsep as [Hs|Hs]; lia.
  - apply (r1_stk_tr W mem mem' _ _ Hwin MU WM). intros x Hx.
    destruct (r1_out_dec W x) as [Ho|Hno]; [left; exact Ho | right; exact (HRD x Hno)].
  - apply (fra_fsrec_stklo B APIf ra g fr [] regs mem mem' md W HFRA MU).
    intros x Hx Hnb. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|[H|H]]; lia.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* FRA across the one stage that writes a frame-shadow byte: the canonical sl_fr_meta. *)
Lemma r1_fra_sh : forall g fr regs mem mem' md (W : list LF.ivl),
  FRA B APIf ra g fr [] regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> AsanRTInv.rt_disjoint W -> shadow_rw mem' ->
  (forall x, ~ LF.outside W x -> Sfr fr + 332 <= x < Sfr fr + 333) ->
  (forall x, ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  FRA B APIf ra g fr [] regs mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr regs mem mem' md W HFRA MU WM HDJ HSW' HWcl HRD.
  destruct (r1_geom g fr regs mem md HFRA) as (HGT & Happ & HfrA & HA416 & HspA & Hsplo & HSAPP & Hstklo4 & HSlo & HSfr).
  unfold ACw.GT in HGT.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); unfold AFw.SLOT_STACK in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply A.Tk.UL.MState.unsigned_lit; exact HA64).
  rewrite HbvA in HfrA, HA416, HspA. rewrite Haspz in HspA, Hsplo, Hstklo4.
  unfold APPMEM_END in HSAPP.
  assert (Happout : forall x, app_mem x -> LF.outside W x).
  { intros x Hx. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. pose proof (HWcl x Hno) as H.
    assert (Hin : in_shadow x) by (replace x with (Sfr fr + (x - Sfr fr)) by lia;
      apply r1_fsh; [exact Happ | lia]).
    pose proof (r1_sh_app_dj x x Hin Hx). lia. }
  destruct (r1_ah g fr regs mem mem' md W HFRA MU WM
              ltac:(intros x Hx; right; left; pose proof (HWcl x Hx); lia) HRD)
    as (HAH' & Hown & HSTK' & HSTKhi').
  assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
  { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
    { split; [lia|]. split; [unfold Sfr, shadow_addr, ASAN_K in *; lia|].
      intros a Ha. apply HSW'. replace a with (Sfr fr + (a - Sfr fr)) by lia.
      apply r1_fsh; [exact Happ | lia]. }
    destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
    exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
  apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs mem mem' md W HFRA MU WM
           (r1_ro_keep W mem mem' Hro MU
              ltac:(intros x Hx; apply Happout; unfold app_mem, LOWMEM_END; left; lia))
           HDJ HAH' HSTK' Happ ltac:(unfold ACw.GT; lia) Hshnew).
  - intros x Hx Hnfr Hnsh. destruct (r1_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. pose proof (HWcl x Hno). apply Hnsh. lia.
  - intros A0 HA0 HA0r x Hx.
    assert (A0 = A) by (rewrite <- HbvA, HA0, A.Tk.UL.MState.unsigned_lit by lia; reflexivity).
    subst A0. apply Happout. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - intros x Hx. apply Happout. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - intros A0 HA0 HA0r x Hx.
    assert (A0 = A) by (rewrite <- HbvA, HA0, A.Tk.UL.MState.unsigned_lit by lia; reflexivity).
    subst A0. apply Happout. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - intros x Hx. left. apply Happout. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right.
    unfold AFw.SLOT_STACK in Hx. lia.
  - intros a Ha. pose proof (r1_ag_range a Ha) as Har.
    apply (r1_addr_keep W mem mem' a 1 (HAG a Ha) MU). intros i Hi.
    replace (a + i) with a by lia.
    destruct (r1_out_dec W (shadow_addr a)) as [Ho|Hno]; [exact Ho|].
    exfalso. pose proof (HWcl _ Hno) as H.
    assert (Hsa : 2147450880 + 16936 <= shadow_addr a <= 2147450880 + 81693)
      by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
    assert (HSfrlo : 2147450880 + 785408 <= Sfr fr)
      by (unfold Sfr, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
    lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(* lia on the arithmetic core of the context: the disjunctions and the non-negated implications of the slot cut
   would make every call case-split exponentially, so they are dropped first (negations are kept). *)
Ltac r1_lean :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?P -> ?Q |- _ =>
             lazymatch Q with
             | False => fail
             | _ => lazymatch type of P with Prop => clear H end
             end
         end.
Ltac r1_lia := r1_lean; lia.

(* Side conditions of the run lemmas: register equations, bounds, and the input/shadow facts at hand. *)
Ltac r1_side :=
  first
    [ assumption
    | (intros ?; assumption)
    | r1_lia
    | (f_equal; r1_lia)
    | (r1_lean; Z.div_mod_to_equations; lia)
    | (intros ? ?; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; r1_lia)
    | (r1_lean; intros ?; exfalso; lia) ].

(* A register of a concrete register map, up to an arithmetic rewrite of its value. *)
Ltac r1_gz e := transitivity e; [reflexivity | f_equal; r1_lia].

(* The frame body, its shadow and everything at or above sp - FN_STACK are rc_away (Seg/RcPro.v), so a run that
   writes only those keeps PRO's input pair: the frame is at or above stklo (real arm; fr mod 32 = 0, so every
   frame granule is 8-aligned) or on the side stack, and stklo <= sp - FN_STACK (fra_win). *)
Lemma r1_away : forall g fr regs mem md x,
  FRA B APIf ra g fr [] regs mem md ->
  (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/ ACw.aspZ regs - FN_STACK <= x ->
  rc_away APIf mem md x.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr regs mem md x HFRA Hx.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & _).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  unfold rc_away.
  destruct Hx as [Hx | [Hx | Hx]].
  - destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    + left. exact (proj1 (Hreal x Hx)).
    + right; left. exact (Hfs x Hx).
  - right; right. exists (fr + 8 * (x - Sfr fr)).
    split; [apply Happ; lia|].
    split; [rewrite r1_sh8; unfold Sfr; lia|].
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    + left. split; [exact (proj1 (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia))) | Z.div_mod_to_equations; lia].
    + right. apply Hfs. lia.
  - left. lia.
Qed.

(* One turn of the our[] loop at the cut 0x81414: the fuzz_u8 arm (left > 0: our[t] = in[t]; left = 0:
   our[t] = 0), then the back edge to turn t + 1, or, after turn 5, the tail to P3 (0x81b14) or, on the odd-mode
   arm, through the three tail stages and the catalogue call to R2 (0x814f8). *)
Lemma r1_turn : forall t,
  (t < 5 -> Hat B APIf ra (Inv_A81414_at B APIf ra) (t + 1)) ->
  Hcut B APIf ra (Inv_A81b14 B APIf ra) ->
  Hcut B APIf ra (Inv_A814f8 B APIf ra) ->
  Hat B APIf ra (Inv_A81414_at B APIf ra) t.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros t Hnext HP3 HR2 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Ht & Hg1 & Hg7 & Hg10 & Hg11 & Hg12 &
                    Hg13 & Hg14 & Hg18 & Hg21 & Hg22 & Hg25 & Hg28 & Hg29 & Hg30 & Hg31 & H152 & HPRO & HSH328 &
                    Hg27 & H144 & H208 & HIDB & HJNK & H280 & H240 & HJY & HSC & H192 & H216 & HOURc).
  pose proof HPRO as (P40 & P120 & P136 & P160 & H168 & P176 & P200 & P248 & HOURA & HINB & HIN &
                      P184 & P256 & P264 & P272).
  subst c.
  destruct (r1_geom g fr regs mem md HFRA)
    as (HGT & Happ & HfrA & HA416 & HspA & Hsplo & HSAPP & Hstklo4 & HSlo & HSfr).
  unfold ACw.GT in HGT.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & _ & _ & Hfrw).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply A.Tk.UL.MState.unsigned_lit; exact HA64).
  rewrite HbvA in HfrA, HA416, HspA. rewrite Haspz in HspA, Hsplo, Hstklo4, Hlo, Hstkw.
  pose proof (Hplace 16 ltac:(lia)) as Hsep16. rewrite Haspz in Hsep16.
  unfold APPMEM_END in HSAPP.
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= 140737488355328).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (HShD : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2.
    unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
  assert (HShA : Sfr fr + FRAME_SHADOW <= A /\ Sfr fr + FRAME_SHADOW <= sp - 16).
  { unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists b, mrd rsegs mem (wa a) = Some b).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (ACw.a_laws_fs_state _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FSb HAH Hw HFSr) as (Hok & _).
      destruct Hok as (Hok1 & _). destruct (Hok1 a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  assert (HWRour : wr_at rsegs mem (fr + 2624) 6).
  { split; [lia|]. split; [lia|]. intros i Hi. exact (Hfrw (fr + 2624 + i) ltac:(lia)). }
  assert (Hsh328 : (fr + 2624 + t) / 8 + ASAN_K = Sfr fr + 328).
  { unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
  assert (HRdour : ov_read_bytes rsegs mem (wa ((fr + 2624 + t) / 8 + ASAN_K)) 1 = Some [Z_to_bv 8 6])
    by (rewrite Hsh328; apply r1_rd1; exact HSH328).
  assert (Hkd6 : bv_signed (Z_to_bv 8 6) = 6) by (vm_compute; reflexivity).
  assert (Hlen : g_n g = Z.of_nat (length (g_in g))) by reflexivity.
  assert (Hdj : 0 < g_n g -> g_p g + g_n g <= fr \/ fr + FRAME_BYTES <= g_p g).
  { intros Hn0. destruct (HIN Hn0) as (HInH & HADp).
    assert (HInH' : In (g_p g, g_n g) ([] ++ g_H g)) by (cbn; exact HInH).
    destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS ([] ++ g_H g) mem md (g_p g) (g_n g) HAH HInH')
      as (_ & Hp4096 & Hple & _ & Hbytes).
    destruct (Z_le_gt_dec (g_p g + g_n g) fr) as [Hle|Hgt]; [left; exact Hle|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) (g_p g)) as [Hle2|Hgt2]; [right; exact Hle2|].
    exfalso.
    destruct (Hbytes (Z.max (g_p g) fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal (Z.max (g_p g) fr) ltac:(lia)). lia.
    - exact (Hnfs (Hfs (Z.max (g_p g) fr) ltac:(lia))). }
  assert (Hpb : 0 < g_n g -> 4096 <= g_p g /\ g_p g + g_n g <= 140737488355328).
  { intros Hn0. destruct (HIN Hn0) as (HInH & HADp).
    assert (HInH' : In (g_p g, g_n g) ([] ++ g_H g)) by (cbn; exact HInH).
    destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS ([] ++ g_H g) mem md (g_p g) (g_n g) HAH HInH')
      as (_ & H4096 & _ & _ & _).
    destruct HADp as (_ & _ & Hpe & _). unfold APPMEM_END in Hpe. split; [exact H4096 | lia]. }
  unfold rg in Hg1, Hg7, Hg10, Hg11, Hg12, Hg13, Hg14, Hg18, Hg21, Hg22, Hg25, Hg27, Hg28, Hg29, Hg30, Hg31,
    Hr2, Hr8, Hr9, Hr19, Hr26.
  destruct HOURc as (junk & Hjl & HOUR).
  assert (HPRElen : length (firstn (Z.to_nat t) (OUR (g_in g))) = Z.to_nat t)
    by (rewrite length_firstn, OUR_length; lia).
  assert (HSTour : store_ok rsegs mem (wa (fr + 2624 + t)) 1 = true)
    by exact (wr_at_store_ok rsegs mem (fr + 2624) 6 t 1 HWRour ltac:(lia) ltac:(cbn; lia)).
  destruct H168 as (A1 & HA1 & Hq168).
  assert (HA1e : A1 = A).
  { pose proof Hq168 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A1 A HA1 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A1.
  destruct H152 as (A2 & HA2 & Hq152).
  assert (HA2e : A2 = A).
  { pose proof Hq152 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A2 A HA2 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A2.
  destruct H144 as (A3 & HA3 & Hq144).
  assert (HA3e : A3 = A).
  { pose proof Hq144 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A3 A HA3 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A3.
  destruct H208 as (A4 & HA4 & Hq208).
  assert (HA4e : A4 = A).
  { pose proof Hq208 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A4 A HA4 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A4.
  destruct H280 as (A5 & HA5 & Hq280).
  assert (HA5e : A5 = A).
  { pose proof Hq280 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A5 A HA5 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A5.
  destruct H240 as (A6 & HA6 & Hq240).
  assert (HA6e : A6 = A).
  { pose proof Hq240 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A6 A HA6 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A6.
  destruct HIDB as (idb & HIDB). destruct HJNK as (fjk & HJNK).
  destruct HJY as (jy & HJY). destruct HSC as (scj & HSC).
  destruct H192 as (A7 & HA7 & Hq192).
  assert (HA7e : A7 = A).
  { pose proof Hq192 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A7 A HA7 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A7.
  destruct H216 as (A8 & HA8 & Hq216).
  assert (HA8e : A8 = A).
  { pose proof Hq216 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A8 A HA8 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite !Z.mod_small in Hm by r1_lia. exact Hm. }
  subst A8.
  set (Wf := [(fr + 2624 + t, fr + 2624 + t + 1)]) in *.
  assert (HWfapp : forall x, ~ LF.outside Wf x -> fr + 2624 + t <= x < fr + 2624 + t + 1)
    by (intros x Hx; unfold Wf in Hx; cbn [LF.outside] in Hx; lia).
  assert (HDJf : AsanRTInv.rt_disjoint Wf).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
      RT_AGLOB, RT_AGLOB_LEN, Wf.
    cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  assert (HAWf : all_app Wf).
  { unfold Wf. cbn [all_app]. split; [|exact I]. unfold app_ivl. intros x Hx. apply Happ. lia. }
  (* PRO across a run that writes our[t] alone *)
  assert (PROf : forall mem' regs'', LF.munch Wf mem mem' -> getr regs'' 9 = getr regs 9 -> PRO g fr regs'' mem').
  { intros mem' regs'' MU E9.
    apply (rc_pro_keep B APIf ra g fr [] regs regs'' mem mem' md Wf A HFRA HPRO MU Hr9
             ltac:(r1_lia) ltac:(unfold APPMEM_END in *; r1_lia) E9).
    - intros x Hx. unfold Wf. cbn [LF.outside].
      split; [destruct Hx as [H|[H|[H|[H|[H|H]]]]]; r1_lia | exact I].
    - intros i Hi. unfold Wf. cbn [LF.outside]. split; [|exact I].
      pose proof (r1_sh_app_dj (shadow_addr (fr + 2624 + i)) (fr + 2624 + t)
                    (shadow_of_app _ (Happ (fr + 2624 + i) ltac:(lia))) (Happ (fr + 2624 + t) ltac:(lia))). lia.
    - intros x Hx. apply (r1_away g fr regs mem md x HFRA). left. pose proof (HWfapp x Hx). lia. }
  (* ---- the three continuations ---- *)
  (* (a) the back edge: the cut of turn t + 1 *)
  assert (NEXT : forall (v : byte) R mem' regs'' md',
            t < 5 -> v = RcIdentModel.nthb (g_in g) (Z.to_nat t) ->
            getr R 1 = getr regs 1 -> getr R 2 = getr regs 2 -> getr R 3 = getr regs 3 ->
            getr R 4 = getr regs 4 -> getr R 7 = getr regs 7 -> getr R 8 = getr regs 8 ->
            getr R 9 = getr regs 9 -> getr R 12 = getr regs 12 -> getr R 13 = getr regs 13 ->
            getr R 18 = getr regs 18 -> getr R 19 = getr regs 19 -> getr R 21 = getr regs 21 ->
            getr R 26 = getr regs 26 -> getr R 27 = getr regs 27 ->
            getr R 28 = getr regs 28 -> getr R 29 = getr regs 29 ->
            getr R 30 = getr regs 30 -> getr R 31 = getr regs 31 ->
            getr R 10 = Z_to_bv 64 (fr + 2624 + (t + 1)) -> getr R 11 = Z_to_bv 64 (t + 1 + 1) ->
            getr R 14 = Z_to_bv 64 (fr + 2624 + (t + 1)) ->
            getr R 22 = Z_to_bv 64 (g_p g + Z.min (t + 1) (g_n g)) ->
            getr R 25 = Z_to_bv 64 (g_n g - Z.min (t + 1) (g_n g)) ->
            LF.munch Wf mem mem' -> LF.wmono rsegs mem mem' ->
            bytes_at rsegs mem' (fr + 2624 + t) [v] ->
            (forall r, getr regs'' r = getr R r) -> AsanLift.mat_le md md' ->
            SR rsegs (mkCfg (mkst regs'' (Z_to_bv 64 0x81414) mem' (seg_rom rsegs)) md') (Post B APIf ra g)).
  { intros v R mem' regs'' md' Ht5 Hv K1 K2 K3 K4 K7 K8 K9 K12 K13 K18 K19 K21 K26 K27 K28 K29 K30 K31
      K10 K11 K14 K22 K25 MU WM HB Hreg Hmat.
    assert (HRDf : forall x, ~ LF.outside Wf x -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply (r1_ba_rd mem' (fr + 2624 + t) [v] x HB). cbn [length]. pose proof (HWfapp x Hx). lia. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r1_fra_app g fr regs regs'' mem mem' md Wf HFRA MU WM HDJf HAWf).
      - intros x Hx. left. pose proof (HWfapp x Hx). lia.
      - exact HRDf.
      - rewrite Hreg; exact K2.
      - rewrite Hreg; exact K3.
      - rewrite Hreg; exact K4.
      - rewrite Hreg; exact K8.
      - rewrite Hreg; exact K9.
      - rewrite Hreg; exact K19.
      - rewrite Hreg; exact K26. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity; exact Hmat).
    destruct (r1_ah g fr regs mem mem' md Wf HFRA MU WM
                ltac:(intros x Hx; left; pose proof (HWfapp x Hx); lia) HRDf)
      as (_ & Hown & HSTK' & HSTKhi').
    assert (HENT' : ENT APIf g [] mem' md).
    { eapply ent_store with (W := Wf); [exact HENT | exact HFRA | exact MU | | | |].
      - intros x _. destruct (r1_out_dec Wf x) as [Ho|Hno]; [left; exact Ho|].
        right; right; left. pose proof (HWfapp x Hno). lia.
      - exact HSTK'.
      - exact HSTKhi'.
      - intros a _ Ha. apply Hown. exact Ha. }
    rewrite <- SEGS. apply (Hnext Ht5).
    exists regs'', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT' | exact Hmat]|].
    split; [exact Hgn|]. split; [lia|].
    unfold spill, rg, q64, b8.
    split; [rewrite Hreg, K1; exact Hg1|].
    split; [rewrite Hreg, K7; exact Hg7|].
    split; [rewrite Hreg; exact K10|].
    split; [rewrite Hreg; exact K11|].
    split; [rewrite Hreg, K12; exact Hg12|].
    split; [rewrite Hreg, K13; exact Hg13|].
    split; [rewrite Hreg; exact K14|].
    split; [rewrite Hreg, K18; exact Hg18|].
    split; [rewrite Hreg, K21; exact Hg21|].
    split; [rewrite Hreg; exact K22|].
    split; [rewrite Hreg; exact K25|].
    split; [rewrite Hreg, K28; exact Hg28|].
    split; [rewrite Hreg, K29; exact Hg29|].
    split; [rewrite Hreg, K30; exact Hg30|].
    split; [rewrite Hreg, K31; exact Hg31|].
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq152 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
    split; [exact (PROf mem' regs'' MU ltac:(rewrite Hreg; exact K9))|].
    split.
    { apply (bytes_at_transport rsegs Wf mem mem' _ _ HSH328 MU).
      cbn [length]. unfold Wf. cbn [disjoint_from]. split; [|exact I].
      pose proof (r1_sh_app_dj (Sfr fr + 328) (fr + 2624 + t)
                    (r1_fsh fr 328 Happ ltac:(lia)) (Happ (fr + 2624 + t) ltac:(lia))). lia. }
    split; [rewrite Hreg, K27; exact Hg27|].
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq144 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [lia | exact I]. }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq208 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [lia | exact I]. }
    split.
    { exists idb. apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HIDB MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
    split.
    { exists fjk. apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HJNK MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq280 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [lia | exact I]. }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq240 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [lia | exact I]. }
    split.
    { exists jy. apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HJY MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
    split.
    { exists scj. apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HSC MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq192 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [lia | exact I]. }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq216 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [lia | exact I]. }
    exists (tl junk). split.
    { destruct junk as [|b0 junk']; cbn [length tl] in *; lia. }
    { pose proof (r1_our_keep mem mem' (fr + 2624) t _ junk v HOUR HPRElen ltac:(lia) ltac:(lia) MU HB) as HH.
      rewrite Hv in HH. rewrite <- (r1_our_step (g_in g) (Z.to_nat t) ltac:(lia)) in HH.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia. exact HH. } }
  (* (b) the P3 exits: our[] is complete *)
  assert (EXITP3 : forall (v : byte) R mem' regs'' md',
            t = 5 -> v = RcIdentModel.nthb (g_in g) (Z.to_nat t) ->
            getr R 2 = getr regs 2 -> getr R 3 = getr regs 3 -> getr R 4 = getr regs 4 ->
            getr R 8 = getr regs 8 -> getr R 9 = getr regs 9 -> getr R 19 = getr regs 19 ->
            getr R 26 = getr regs 26 -> getr R 27 = getr regs 27 ->
            (* the cursor at c0 = min n 7 on all three 0x81b14 arms (for CUR g (c0 (g_in g)) at P3) *)
            getr R 22 = Z_to_bv 64 (g_p g + Z.min (g_n g) 7) ->
            getr R 25 = Z_to_bv 64 (g_n g - Z.min (g_n g) 7) ->
            LF.munch Wf mem mem' -> LF.wmono rsegs mem mem' ->
            bytes_at rsegs mem' (fr + 2624 + t) [v] ->
            (forall r, getr regs'' r = getr R r) -> AsanLift.mat_le md md' ->
            SR rsegs (mkCfg (mkst regs'' (Z_to_bv 64 0x81b14) mem' (seg_rom rsegs)) md') (Post B APIf ra g)).
  { intros v R mem' regs'' md' Ht5 Hv K2 K3 K4 K8 K9 K19 K26 K27 K22 K25 MU WM HB Hreg Hmat.
    assert (HRDf : forall x, ~ LF.outside Wf x -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply (r1_ba_rd mem' (fr + 2624 + t) [v] x HB). cbn [length]. pose proof (HWfapp x Hx). lia. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r1_fra_app g fr regs regs'' mem mem' md Wf HFRA MU WM HDJf HAWf).
      - intros x Hx. left. pose proof (HWfapp x Hx). lia.
      - exact HRDf.
      - rewrite Hreg; exact K2.
      - rewrite Hreg; exact K3.
      - rewrite Hreg; exact K4.
      - rewrite Hreg; exact K8.
      - rewrite Hreg; exact K9.
      - rewrite Hreg; exact K19.
      - rewrite Hreg; exact K26. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity; exact Hmat).
    destruct (r1_ah g fr regs mem mem' md Wf HFRA MU WM
                ltac:(intros x Hx; left; pose proof (HWfapp x Hx); lia) HRDf)
      as (_ & Hown & HSTK' & HSTKhi').
    assert (HENT' : ENT APIf g [] mem' md).
    { eapply ent_store with (W := Wf); [exact HENT | exact HFRA | exact MU | | | |].
      - intros x _. destruct (r1_out_dec Wf x) as [Ho|Hno]; [left; exact Ho|].
        right; right; left. pose proof (HWfapp x Hno). lia.
      - exact HSTK'.
      - exact HSTKhi'.
      - intros a _ Ha. apply Hown. exact Ha. }
    rewrite <- SEGS. apply HP3.
    exists regs'', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT' | exact Hmat]|].
    split; [exact Hgn|].
    split.
    { unfold OURb.
      pose proof (r1_our_keep mem mem' (fr + 2624) t _ junk v HOUR HPRElen ltac:(lia) ltac:(lia) MU HB) as HH.
      rewrite Hv in HH. rewrite <- (r1_our_step (g_in g) (Z.to_nat t) ltac:(lia)) in HH.
      replace (tl junk) with (@nil byte) in HH
        by (destruct junk as [|b0 [|b1 r']]; cbn [length] in Hjl; try lia; reflexivity).
      rewrite app_nil_r in HH.
      rewrite firstn_all2 in HH by (rewrite OUR_length; lia). exact HH. }
    split.
    { unfold CUR, rg.
      split; [change (SlotModel.c0 (g_in g)) with (Z.min (g_n g) 7); r1_lia|].
      split; [rewrite Hreg; exact K22 | rewrite Hreg; exact K25]. }
    split; [exact (PROf mem' regs'' MU ltac:(rewrite Hreg; exact K9))|].
    split.
    { exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|]. unfold q64.
      apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq144 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [r1_lia | exact I]. }
    exists sp, A, idb, fjk.
    split; [rewrite Hreg, K2; exact Hr2|].
    split; [rewrite Hreg, K9; exact Hr9|].
    split; [unfold rg; rewrite Hreg, K27; exact Hg27|].
    split; [exact HA64|].
    split; [r1_lia|].
    split.
    { apply (r1_c8 Wf mem mem' (A + 192) _ _ _ Hq208 Hwin); [r1_lia | r1_lia | exact MU | exact WM |].
      unfold Wf. cbn [disjoint_from]. split; [r1_lia | exact I]. }
    split.
    { apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HIDB MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [r1_lia | exact I]. }
    split.
    { apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HJNK MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [r1_lia | exact I]. }
    split.
    { unfold q64. apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq280 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [r1_lia | exact I]. }
    split.
    { unfold q64. apply (bytes_at_transport rsegs Wf mem mem' _ _ Hq240 MU).
      rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [r1_lia | exact I]. }
    exists jy, scj. split.
    { apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HJY MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [r1_lia | exact I]. }
    { apply (LF.rw_cells_transport rsegs Wf mem mem' _ _ HSC MU WM).
      unfold Wf. cbn [disjoint_from cells_size csize Nat.add]. split; [r1_lia | exact I]. } }
  (* (c) the R2 exit, after the three tail stages *)
  set (W1 := [(fr + 2624 + t, fr + 2624 + t + 1); (A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)]) in *.
  set (W2 := [(Sfr fr + 332, Sfr fr + 333)]) in *.
  set (W3 := [(fr + 2656, fr + 2664); (sp - 16, sp)]) in *.
  assert (EXITR2 : forall R ma mb mem' regs'' md',
            t = 5 -> 7 <= g_n g ->
            getr R 2 = getr regs 2 -> getr R 3 = getr regs 3 -> getr R 4 = getr regs 4 ->
            getr R 8 = getr regs 8 -> getr R 9 = getr regs 9 -> getr R 19 = getr regs 19 ->
            getr R 26 = getr regs 26 -> getr R 18 = getr regs 18 -> getr R 21 = getr regs 21 ->
            getr R 10 = Z_to_bv 64 CAT ->
            getr R 22 = Z_to_bv 64 (g_p g + 7) -> getr R 25 = Z_to_bv 64 (g_n g - 7) ->
            getr R 23 = Z_to_bv 64 (mode (g_in g)) ->
            LF.munch W1 mem ma -> LF.wmono rsegs mem ma ->
            bytes_at rsegs ma (fr + 2624) (OUR (g_in g)) -> stk rsegs ma (A + 48) (A + 136) ->
            LF.munch W2 ma mb -> LF.wmono rsegs ma mb -> shadow_rw mb ->
            bytes_at rsegs mb (Sfr fr + 332) [Z_to_bv 8 0] ->
            LF.munch W3 mb mem' -> LF.wmono rsegs mb mem' ->
            stk rsegs mem' (sp - 16) sp ->
            q64 mem' (fr + 2656) 11 -> q64 mem' (A + 48) (fr + 2256) -> q64 mem' (A + 128) (fr + 544) ->
            q64 mem' (A + 56) (fr + 2368) -> q64 mem' (A + 72) (fr + 2496) ->
            q64 mem' (A + 80) (fr + 2464) -> q64 mem' (A + 88) (fr + 2448) ->
            (forall r, getr regs'' r = getr R r) -> AsanLift.mat_le md md' ->
            SR rsegs (mkCfg (mkst regs'' (Z_to_bv 64 0x814f8) mem' (seg_rom rsegs)) md') (Post B APIf ra g)).
  { intros R ma mb mem' regs'' md' Ht5 Hn7 K2 K3 K4 K8 K9 K19 K26 K18 K21 K10 K22 K25 K23
      MU1 WM1 HOURa STAa MU2 WM2 HSWb HSHb MU3 WM3 STw HZc HZ48 HZ128 HZ56 HZ72 HZ80 HZ88 Hreg Hmat.
    (* stage 1: the our[5] byte and the spills *)
    assert (HDJ1 : AsanRTInv.rt_disjoint W1)
      by (unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN, W1; cbn [disjoint_from]; repeat split; first [exact I | lia]).
    assert (HAW1 : all_app W1).
    { unfold W1. cbn [all_app]. split; [unfold app_ivl; intros x Hx; apply Happ; lia|].
      repeat split; unfold app_ivl; intros x Hx; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia. }
    assert (HRD1 : forall x, ~ LF.outside W1 x -> exists b, mrd rsegs ma (wa x) = Some b).
    { intros x Hx. unfold W1 in Hx. cbn [LF.outside] in Hx.
      destruct (Z_lt_ge_dec x (fr + 2624 + t + 1)) as [H1|H1].
      - apply (r1_ba_rd ma (fr + 2624) (OUR (g_in g)) x HOURa). rewrite OUR_length. r1_lia.
      - destruct STAa as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    assert (HFRA1 : FRA B APIf ra g fr [] regs ma md).
    { apply (r1_fra_app g fr regs regs mem ma md W1 HFRA MU1 WM1 HDJ1 HAW1); try reflexivity.
      - intros x Hx. unfold W1 in Hx. cbn [LF.outside] in Hx. rewrite HbvA.
        destruct (Z_lt_ge_dec x (fr + 2624 + t + 1)) as [H1|H1]; [left; r1_lia | right; left; r1_lia].
      - exact HRD1. }
    destruct (r1_ah g fr regs mem ma md W1 HFRA MU1 WM1
                ltac:(intros x Hx; unfold W1 in Hx; cbn [LF.outside] in Hx;
                      destruct (Z_lt_ge_dec x (fr + 2624 + t + 1)) as [H1|H1];
                      [left; r1_lia | right; right; unfold APPMEM_END; r1_lia]) HRD1)
      as (_ & Hown1 & HSTK1 & HSTKhi1).
    assert (HENT1 : ENT APIf g [] ma md).
    { eapply ent_store with (W := W1); [exact HENT | exact HFRA | exact MU1 | | | |].
      - intros x _. destruct (r1_out_dec W1 x) as [Ho|Hno]; [left; exact Ho|].
        unfold W1 in Hno. cbn [LF.outside] in Hno.
        destruct (Z_lt_ge_dec x (fr + 2624 + t + 1)) as [H1|H1]; [right; right; left; r1_lia | right; left; r1_lia].
      - exact HSTK1.
      - exact HSTKhi1.
      - intros a _ Ha. apply Hown1. exact Ha. }
    (* stage 2: the count cell's shadow byte *)
    assert (HDJ2 : AsanRTInv.rt_disjoint W2)
      by (unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN, W2; cbn [disjoint_from]; repeat split; first [exact I | lia]).
    assert (HRD2 : forall x, ~ LF.outside W2 x -> exists b, mrd rsegs mb (wa x) = Some b).
    { intros x Hx. unfold W2 in Hx. cbn [LF.outside] in Hx.
      apply (r1_ba_rd mb (Sfr fr + 332) [Z_to_bv 8 0] x HSHb). cbn [length]. lia. }
    assert (HFRA2 : FRA B APIf ra g fr [] regs mb md).
    { apply (r1_fra_sh g fr regs ma mb md W2 HFRA1 MU2 WM2 HDJ2 HSWb).
      - intros x Hx. unfold W2 in Hx. cbn [LF.outside] in Hx. lia.
      - exact HRD2. }
    destruct (r1_ah g fr regs ma mb md W2 HFRA1 MU2 WM2
                ltac:(intros x Hx; unfold W2 in Hx; cbn [LF.outside] in Hx; right; left; lia) HRD2)
      as (_ & Hown2 & HSTK2 & HSTKhi2).
    assert (HENT2 : ENT APIf g [] mb md).
    { eapply ent_store with (W := W2); [exact HENT1 | exact HFRA1 | exact MU2 | | | |].
      - intros x _. destruct (r1_out_dec W2 x) as [Ho|Hno]; [left; exact Ho|].
        unfold W2 in Hno. cbn [LF.outside] in Hno. right; right; right. lia.
      - exact HSTK2.
      - exact HSTKhi2.
      - intros a _ Ha. apply Hown2. exact Ha. }
    (* stage 3: the count cell and the callee window *)
    assert (HDJ3 : AsanRTInv.rt_disjoint W3)
      by (unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN, W3; cbn [disjoint_from]; repeat split; first [exact I | lia]).
    assert (HAW3 : all_app W3).
    { unfold W3. cbn [all_app]. split; [unfold app_ivl; intros x Hx; apply Happ; lia|].
      split; [|exact I]. unfold app_ivl. intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
    assert (HRD3 : forall x, ~ LF.outside W3 x -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. unfold W3 in Hx. cbn [LF.outside] in Hx.
      destruct (Z_lt_ge_dec x (fr + 2664)) as [H1|H1]; [destruct (Z_le_gt_dec (fr + 2656) x) as [H2|H2]|].
      - apply (r1_ba_rd mem' (fr + 2656) (le8 (Z_to_bv 64 11)) x HZc). rewrite length_le8. lia.
      - destruct STw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r1_fra_app g fr regs regs'' mb mem' md W3 HFRA2 MU3 WM3 HDJ3 HAW3).
      - intros x Hx. unfold W3 in Hx. cbn [LF.outside] in Hx. rewrite Haspz.
        destruct (Z_lt_ge_dec x (fr + 2664)) as [H1|H1]; [destruct (Z_le_gt_dec (fr + 2656) x) as [H2|H2]|];
          [left; lia | right; right; lia | right; right; lia].
      - exact HRD3.
      - rewrite Hreg; exact K2.
      - rewrite Hreg; exact K3.
      - rewrite Hreg; exact K4.
      - rewrite Hreg; exact K8.
      - rewrite Hreg; exact K9.
      - rewrite Hreg; exact K19.
      - rewrite Hreg; exact K26. }
    destruct (r1_geom g fr regs mb md HFRA2) as (_ & _ & _ & _ & _ & _ & _ & Hstklo4b & _ & _).
    rewrite Haspz in Hstklo4b.
    destruct (r1_ah g fr regs mb mem' md W3 HFRA2 MU3 WM3
                ltac:(intros x Hx; unfold W3 in Hx; cbn [LF.outside] in Hx;
                      destruct (Z_lt_ge_dec x (fr + 2664)) as [H1|H1];
                      [destruct (Z_le_gt_dec (fr + 2656) x) as [H2|H2]|];
                      [left; r1_lia | right; right; unfold APPMEM_END; r1_lia | right; right; unfold APPMEM_END; r1_lia])
                HRD3)
      as (_ & Hown3 & HSTK3 & HSTKhi3).
    assert (HENT3 : ENT APIf g [] mem' md).
    { eapply ent_store with (W := W3); [exact HENT2 | exact HFRA2 | exact MU3 | | | |].
      - intros x _. destruct (r1_out_dec W3 x) as [Ho|Hno]; [left; exact Ho|].
        unfold W3 in Hno. cbn [LF.outside] in Hno.
        destruct (Z_lt_ge_dec x (fr + 2664)) as [H1|H1]; [destruct (Z_le_gt_dec (fr + 2656) x) as [H2|H2]|];
          [right; right; left; r1_lia | right; left; r1_lia | right; left; r1_lia].
      - exact HSTK3.
      - exact HSTKhi3.
      - intros a _ Ha. apply Hown3. exact Ha. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity; exact Hmat).
    (* the cut at 0x814f8 *)
    assert (MU23 : LF.munch [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)] ma mem').
    { apply (munch_trans _ ma mb mem').
      - apply (munch_weaken W2); [unfold W2; intros x Hx; cbn [LF.outside] in Hx |- *; clear - Hx; tauto | exact MU2].
      - apply (munch_weaken W3); [unfold W3; intros x Hx; cbn [LF.outside] in Hx |- *; clear - Hx; tauto | exact MU3]. }
    assert (MUall : LF.munch [(fr + 2624 + t, fr + 2624 + t + 1); (A + 48, A + 64); (A + 72, A + 96);
                              (A + 128, A + 136); (Sfr fr + 332, Sfr fr + 333);
                              (fr + 2656, fr + 2664); (sp - 16, sp)] mem mem').
    { apply (munch_trans _ mem ma mem').
      - apply (munch_weaken W1); [unfold W1; intros x Hx; cbn [LF.outside] in Hx |- *; clear - Hx; tauto | exact MU1].
      - apply (munch_weaken [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)]);
          [intros x Hx; cbn [LF.outside] in Hx |- *; clear - Hx; tauto | exact MU23]. }
    pose proof (wmono_trans rsegs mem ma mem' WM1 (wmono_trans rsegs ma mb mem' WM2 WM3)) as WMall.
    (* PRO: the stores miss the eight spills (the spill stage writes [A + 48, A + 64), [A + 72, A + 96) and
       [A + 128, A + 136) only) and S(fr) + 328, and every written byte is rc_away *)
    assert (HPRO' : PRO g fr regs'' mem').
    { apply (rc_pro_keep B APIf ra g fr [] regs regs'' mem mem' md _ A HFRA HPRO MUall Hr9
               ltac:(r1_lia) ltac:(unfold APPMEM_END in *; r1_lia) ltac:(rewrite Hreg; exact K9)).
      - intros x Hx. destruct HShA as (HsA & Hsp).
        destruct Hx as [H|[H|[H|[H|[H|H]]]]]; cbn [LF.outside]; repeat split; first [exact I | r1_lia].
      - intros i Hi. cbn [LF.outside].
        assert (Hs : shadow_addr (fr + 2624 + i) = Sfr fr + 328)
          by (unfold Sfr, shadow_addr; r1_lean; Z.div_mod_to_equations; lia).
        rewrite Hs. destruct HShD as [Hd|Hd]; destruct HShA as (HsA & Hsp);
          repeat split; first [exact I | r1_lia].
      - intros x Hx. apply (r1_away g fr regs mem md x HFRA). rewrite Haspz.
        repeat (apply r1_notout_cons in Hx; destruct Hx as [Hx|Hx]; [r1_lia|]).
        exfalso. apply Hx. exact I. }
    rewrite <- SEGS. apply HR2.
    exists regs'', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT3 | exact Hmat]|].
    split; [exact Hgn|].
    unfold a0v, OURb, spill, CUR, rg, q64, CAT_N, CAT.
    split; [rewrite Hreg; exact K10|].
    split.
    { apply (bytes_at_transport rsegs _ ma mem' _ _ HOURa MU23).
      rewrite OUR_length. cbn [disjoint_from].
      destruct HShD as [Hs|Hs]; destruct Hsep16 as [Hw|Hw]; repeat split; (exact I || lia). }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq152 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
    split; [rewrite Hreg, K18; exact Hg18|].
    split; [exact HZc|].
    split; [rewrite Hreg, K21; exact Hg21|].
    split; [split; [lia|]; split; [rewrite Hreg; exact K22 | rewrite Hreg; exact K25]|].
    split; [exists A; split; [rewrite Hreg, K9; exact Hr9 | exact HZ48]|].
    split; [exists A; split; [rewrite Hreg, K9; exact Hr9 | exact HZ128]|].
    split; [exact HPRO'|].
    split; [rewrite Hreg; exact K23|].
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq144 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq208 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
    split.
    { exists idb. apply (LF.rw_cells_transport rsegs _ mem mem' _ _ HIDB MUall WMall).
      cbn [disjoint_from cells_size csize Nat.add].
      destruct HShD as [Hs|Hs]; destruct Hsep16 as [Hw|Hw]; repeat split; (exact I || lia). }
    split.
    { exists fjk. apply (LF.rw_cells_transport rsegs _ mem mem' _ _ HJNK MUall WMall).
      cbn [disjoint_from cells_size csize Nat.add].
      destruct HShD as [Hs|Hs]; destruct Hsep16 as [Hw|Hw]; repeat split; (exact I || lia). }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq280 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq240 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
    split.
    { exists jy. apply (LF.rw_cells_transport rsegs _ mem mem' _ _ HJY MUall WMall).
      cbn [disjoint_from cells_size csize Nat.add].
      destruct HShD as [Hs|Hs]; destruct Hsep16 as [Hw|Hw]; repeat split; (exact I || lia). }
    split.
    { exists scj. apply (LF.rw_cells_transport rsegs _ mem mem' _ _ HSC MUall WMall).
      cbn [disjoint_from cells_size csize Nat.add].
      destruct HShD as [Hs|Hs]; destruct Hsep16 as [Hw|Hw]; repeat split; (exact I || lia). }
    split; [exists A; split; [rewrite Hreg, K9; exact Hr9 | exact HZ56]|].
    split; [exists A; split; [rewrite Hreg, K9; exact Hr9 | exact HZ88]|].
    split; [exists A; split; [rewrite Hreg, K9; exact Hr9 | exact HZ80]|].
    split; [exists A; split; [rewrite Hreg, K9; exact Hr9 | exact HZ72]|].
    split.
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq192 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
    { exists A. split; [rewrite Hreg, K9; exact Hr9|].
      apply (bytes_at_transport rsegs _ mem mem' _ _ Hq216 MUall).
      rewrite length_le8. cbn [disjoint_from]. destruct HShA as (HsA & Hsp). repeat split; (exact I || lia). }
  }
  (* ---- the run ---- *)
  assert (Hfr8 : fr mod 8 = 0) by (r1_lean; Z.div_mod_to_equations; lia).
  assert (Hshc : shadow_addr (fr + 2656) = Sfr fr + 332)
    by (unfold Sfr, shadow_addr; r1_lean; Z.div_mod_to_equations; lia).
  assert (Hsep2664 : fr + 2664 <= sp - 16 \/ sp <= fr) by (destruct Hsep16; r1_lia).
  assert (HOKd : bv_signed (Z_to_bv 8 6) = 0 \/ t < bv_signed (Z_to_bv 8 6)) by (right; rewrite Hkd6; r1_lia).
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81414) mem md
    (fun R pc' mem' =>
       (exists v : byte,
          pc' = Z_to_bv 64 0x81414 /\ t < 5 /\ v = RcIdentModel.nthb (g_in g) (Z.to_nat t) /\
          getr R 1 = getr regs 1 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
          getr R 4 = getr regs 4 /\ getr R 7 = getr regs 7 /\ getr R 8 = getr regs 8 /\
          getr R 9 = getr regs 9 /\ getr R 12 = getr regs 12 /\ getr R 13 = getr regs 13 /\
          getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\ getr R 28 = getr regs 28 /\
          getr R 29 = getr regs 29 /\
          getr R 30 = getr regs 30 /\ getr R 31 = getr regs 31 /\
          getr R 10 = Z_to_bv 64 (fr + 2624 + (t + 1)) /\ getr R 11 = Z_to_bv 64 (t + 1 + 1) /\
          getr R 14 = Z_to_bv 64 (fr + 2624 + (t + 1)) /\
          getr R 22 = Z_to_bv 64 (g_p g + Z.min (t + 1) (g_n g)) /\
          getr R 25 = Z_to_bv 64 (g_n g - Z.min (t + 1) (g_n g)) /\
          LF.munch Wf mem mem' /\ LF.wmono rsegs mem mem' /\
          bytes_at rsegs mem' (fr + 2624 + t) [v])
       \/
       (exists v : byte,
          pc' = Z_to_bv 64 0x81b14 /\ t = 5 /\ v = RcIdentModel.nthb (g_in g) (Z.to_nat t) /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 22 = Z_to_bv 64 (g_p g + Z.min (g_n g) 7) /\ getr R 25 = Z_to_bv 64 (g_n g - Z.min (g_n g) 7) /\
          LF.munch Wf mem mem' /\ LF.wmono rsegs mem mem' /\
          bytes_at rsegs mem' (fr + 2624 + t) [v])
       \/
       (exists ma mb : word -> option byte,
          pc' = Z_to_bv 64 0x814f8 /\ t = 5 /\ 7 <= g_n g /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
          getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 21 = getr regs 21 /\
          getr R 10 = Z_to_bv 64 CAT /\
          getr R 22 = Z_to_bv 64 (g_p g + 7) /\ getr R 25 = Z_to_bv 64 (g_n g - 7) /\
          getr R 23 = Z_to_bv 64 (mode (g_in g)) /\
          LF.munch W1 mem ma /\ LF.wmono rsegs mem ma /\
          bytes_at rsegs ma (fr + 2624) (OUR (g_in g)) /\ stk rsegs ma (A + 48) (A + 136) /\
          LF.munch W2 ma mb /\ LF.wmono rsegs ma mb /\ shadow_rw mb /\
          bytes_at rsegs mb (Sfr fr + 332) [Z_to_bv 8 0] /\
          LF.munch W3 mb mem' /\ LF.wmono rsegs mb mem' /\
          stk rsegs mem' (sp - 16) sp /\
          q64 mem' (fr + 2656) 11 /\ q64 mem' (A + 48) (fr + 2256) /\ q64 mem' (A + 128) (fr + 544) /\
          q64 mem' (A + 56) (fr + 2368) /\ q64 mem' (A + 72) (fr + 2496) /\
          q64 mem' (A + 80) (fr + 2464) /\ q64 mem' (A + 88) (fr + 2448)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - cbn [Regs6ss.mkR_of].
    destruct (Z_lt_ge_dec t (g_n g)) as [Hlt | Hge].
    + (* left > 0: our[t] = in[t] *)
      assert (Hmin : Z.min t (g_n g) = t) by r1_lia.
      rewrite Hmin in Hg22, Hg25.
      destruct (HIN ltac:(r1_lia)) as (HInH & HADp).
      destruct (Hpb ltac:(r1_lia)) as (Hp0 & Hpn).
      assert (HADt : addressable mem (g_p g + t) 1) by (apply (r1_addr_sub mem (g_p g) (g_n g) t HADp); r1_lia).
      destruct (meta_byte mem (g_p g + t) 1 HADt ltac:(r1_lia)) as (kq & HROq & Hokq & Hinq).
      assert (HOKq : bv_signed kq = 0 \/ (g_p g + t) mod 8 < bv_signed kq)
        by (destruct Hokq as [H|H]; [left; exact H | right; r1_lia]).
      assert (HRq : ov_read_bytes rsegs mem (wa ((g_p g + t) / 8 + ASAN_K)) 1 = Some [kq]).
      { pose proof (ro_cells_read rsegs mem _ [C1 kq] 0%nat (C1 kq) HROq ltac:(reflexivity)) as HH.
        cbn [csize cbytes] in HH. change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r in HH.
        rewrite rc_shr3 in HH. exact HH. }
      assert (HRb : ov_read_bytes rsegs mem (wa (g_p g + t)) 1
                    = Some [RcIdentModel.nthb (g_in g) (Z.to_nat t)]).
      { apply (r1_rd_at mem (g_p g) (g_in g) t); [exact HINB | r1_lia |].
        unfold RcIdentModel.nthb. apply nth_error_nth'. r1_lia. }
      destruct (Z.eq_dec t 5) as [E5 | N5].
      * (* turn 5: the mode read, then P3 or the tail through the catalogue call *)
        eapply evt_cut.
        { apply r1_ld_evt with (ou := fr + 2624) (t := t) (K := ASAN_K) (A := A) (q := g_p g + t)
            (v := g_n g - t) (b := RcIdentModel.nthb (g_in g) (Z.to_nat t)) (kq := kq) (kd := Z_to_bv 8 6);
            r1_side. }
        intros ms1 (x5 & x6 & x7 & m1 & Ems & MU1 & WM1 & HB1).
        rewrite (proj2 (Z.eqb_eq t 5) E5) in Ems. cbv iota in Ems. subst ms1.
        assert (HOUR1 : bytes_at rsegs m1 (fr + 2624) (OUR (g_in g))).
        { pose proof (r1_our_keep mem m1 (fr + 2624) t _ junk (RcIdentModel.nthb (g_in g) (Z.to_nat t))
                        HOUR HPRElen ltac:(r1_lia) ltac:(r1_lia) MU1 HB1) as HH.
          replace (tl junk) with (@nil byte) in HH
            by (destruct junk as [|b0 [|b1 r']]; cbn [length] in Hjl; try r1_lia; reflexivity).
          rewrite app_nil_r in HH.
          rewrite <- (r1_our_step (g_in g) (Z.to_nat t) ltac:(r1_lia)) in HH.
          rewrite firstn_all2 in HH by (rewrite OUR_length; r1_lia). exact HH. }
        assert (HINB1 : bytes_at rsegs m1 (g_p g) (g_in g)).
        { apply (bytes_at_transport rsegs Wf mem m1 _ _ HINB MU1).
          rewrite <- Hlen. unfold Wf. cbn [disjoint_from]. split; [|exact I].
          destruct (Hdj ltac:(r1_lia)) as [H|H]; [left | right]; r1_lia. }
        assert (HM : g_n g - 6 <> 0 ->
                  exists km : byte,
                    ov_read_bytes rsegs m1 (wa ((g_p g + 6) / 8 + ASAN_K)) 1 = Some [km] /\
                    (bv_signed km = 0 \/ (g_p g + 6) mod 8 < bv_signed km)).
        { intros Hn6.
          assert (HAD6 : addressable mem (g_p g + 6) 1)
            by (apply (r1_addr_sub mem (g_p g) (g_n g) 6 HADp); r1_lia).
          destruct (meta_byte mem (g_p g + 6) 1 HAD6 ltac:(r1_lia)) as (km & HROm & Hokm & Hinm).
          exists km. split.
          - assert (HROm1 : ro_cells rsegs m1 (Z.shiftr (g_p g + 6) 3 + ASAN_K) [C1 km]).
            { apply (ro_cells_transport rsegs Wf mem m1 _ _ HROm MU1).
              cbn [cells_size csize]. unfold Wf. cbn [disjoint_from]. split; [|exact I].
              destruct (r1_sh_app_dj _ _ Hinm (Happ (fr + 2624 + t) ltac:(r1_lia))) as [Hd|Hd]; r1_lia. }
            pose proof (ro_cells_read rsegs m1 _ [C1 km] 0%nat (C1 km) HROm1 ltac:(reflexivity)) as HH.
            cbn [csize cbytes] in HH. change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r in HH.
            rewrite rc_shr3 in HH. exact HH.
          - destruct Hokm as [H|H]; [left; exact H | right; r1_lia]. }
        assert (HRm1 : g_n g - 6 <> 0 ->
                  ov_read_bytes rsegs m1 (wa (g_p g + 6)) 1 = Some [RcIdentModel.nthb (g_in g) 6%nat]).
        { intros Hn6. apply (r1_rd_at m1 (g_p g) (g_in g) 6); [exact HINB1 | r1_lia |].
          unfold RcIdentModel.nthb. apply nth_error_nth'. r1_lia. }
        (* the windows and cells the tail writes, at m1 *)
        assert (Hin332 : in_shadow (Sfr fr + 332)) by (apply r1_fsh; [exact Happ | r1_lia]).
        assert (HAC1 : asan_cells m1).
        { apply (asan_cells_kept _ mem m1 HAC0 MU1). unfold Wf. cbn [disjoint_from]. unfold RT_LO, RT_HI.
          repeat split; first [exact I | r1_lia]. }
        assert (HSW1 : shadow_rw m1).
        { apply (r1_shadow_rw Wf mem m1 HSW0 MU1 WM1). intros a Ha. left.
          unfold Wf. cbn [LF.outside]. split; [|exact I].
          destruct (r1_sh_app_dj a (fr + 2624 + t) Ha (Happ (fr + 2624 + t) ltac:(r1_lia))) as [Hd|Hd]; r1_lia. }
        assert (STA1 : stk rsegs m1 (A + 48) (A + 136)).
        { destruct (stk_split rsegs mem _ (A + 48) _ Hwin ltac:(r1_lia)) as (_ & Hw1).
          destruct (stk_split rsegs mem (A + 48) (A + 136) _ Hw1 ltac:(r1_lia)) as (Hw2 & _).
          apply (r1_stk_tr Wf mem m1 _ _ Hw2 MU1 WM1). intros x Hx. left.
          unfold Wf. cbn [LF.outside]. split; [r1_lia | exact I]. }
        assert (STw1 : stk rsegs m1 (sp - 16) sp).
        { destruct (stk_split rsegs mem _ (sp - 16) _ Hstkw ltac:(r1_lia)) as (_ & Hw16).
          apply (r1_stk_tr Wf mem m1 _ _ Hw16 MU1 WM1). intros x Hx. left.
          unfold Wf. cbn [LF.outside]. split; [destruct Hsep16 as [Hs|Hs]; r1_lia | exact I]. }
        assert (STc1 : stk rsegs m1 (fr + 2656) (fr + 2664)).
        { destruct (stk_split rsegs mem fr (fr + 2656) (fr + FRAME_BYTES) Hfstk ltac:(r1_lia)) as (_ & Hc1).
          destruct (stk_split rsegs mem (fr + 2656) (fr + 2664) (fr + FRAME_BYTES) Hc1 ltac:(r1_lia)) as (Hc2 & _).
          apply (r1_stk_tr Wf mem m1 _ _ Hc2 MU1 WM1). intros x Hx. left.
          unfold Wf. cbn [LF.outside]. split; [r1_lia | exact I]. }
        destruct (r1_cell8 m1 _ _ (fr + 2656) STc1 ltac:(r1_lia) ltac:(r1_lia)) as (cs & CHc).
        destruct (r1_cell8 m1 _ _ (A + 48) STA1 ltac:(r1_lia) ltac:(r1_lia)) as (x48 & CH48).
        destruct (r1_cell8 m1 _ _ (A + 56) STA1 ltac:(r1_lia) ltac:(r1_lia)) as (x56 & CH56).
        destruct (r1_cell8 m1 _ _ (A + 72) STA1 ltac:(r1_lia) ltac:(r1_lia)) as (x72 & CH72).
        destruct (r1_cell8 m1 _ _ (A + 80) STA1 ltac:(r1_lia) ltac:(r1_lia)) as (x80 & CH80).
        destruct (r1_cell8 m1 _ _ (A + 88) STA1 ltac:(r1_lia) ltac:(r1_lia)) as (x88 & CH88).
        destruct (r1_cell8 m1 _ _ (A + 128) STA1 ltac:(r1_lia) ltac:(r1_lia)) as (x128 & CH128).
        assert (STsh1 : stk rsegs m1 (Sfr fr + 332) (Sfr fr + 332 + 1)).
        { split; [r1_lia|]. split; [r1_lia|]. intros a Ha. replace a with (Sfr fr + 332) by r1_lia.
          exact (HSW1 _ Hin332). }
        destruct (r1_cell1 m1 (Sfr fr + 332) STsh1) as (sh1 & CHsh).
        destruct (Z.eq_dec (g_n g - 6) 0) as [Hw6 | Hwn].
        -- (* n = 6: the left = 0 arm 0x81984 to P3 *)
           eapply evt_mono.
           ++ apply r1_mode_evt with (pm := g_p g + 6) (w := g_n g - 6) (K := ASAN_K)
                (bm := Z_to_bv 8 0) (km := Z_to_bv 8 0); r1_side.
           ++ intros ms2 [ (R & E2 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25)
                         | (Hodd & Hw & x0 & x1 & E2) ];
                [| exfalso; r1_lia].
              subst ms2. exists R, (Z_to_bv 64 0x81b14), m1. split; [reflexivity|].
              right; left. exists (RcIdentModel.nthb (g_in g) (Z.to_nat t)).
              split; [reflexivity|]. split; [exact E5|]. split; [reflexivity|].
              split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|].
              split; [exact K9|]. split; [exact K19|]. split; [exact K26|]. split; [exact K27|].
              rewrite (proj2 (Z.eqb_eq (g_n g - 6) 0) Hw6) in K22, K25.
              split; [transitivity (Z_to_bv 64 (g_p g + 6)); [exact K22 | f_equal; r1_lia]|].
              split; [transitivity (Z_to_bv 64 0); [exact K25 | f_equal; r1_lia]|].
              split; [exact MU1|]. split; [exact WM1 | exact HB1].
        -- (* n >= 7: the mode byte decides *)
           destruct (HM Hwn) as (km & HRk1 & HOKk1).
           pose proof (HRm1 Hwn) as HRm1'.
           eapply evt_cut.
           { apply r1_mode_evt with (pm := g_p g + 6) (w := g_n g - 6) (K := ASAN_K)
               (bm := RcIdentModel.nthb (g_in g) 6%nat) (km := km); r1_side. }
           intros ms2 [ (R & E2 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25)
                      | (Hodd & Hw & x0 & x1 & E2) ].
           ++ (* even mode: P3 *)
              subst ms2. apply evt_done. exists R, (Z_to_bv 64 0x81b14), m1. split; [reflexivity|].
              right; left. exists (RcIdentModel.nthb (g_in g) (Z.to_nat t)).
              split; [reflexivity|]. split; [exact E5|]. split; [reflexivity|].
              split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|].
              split; [exact K9|]. split; [exact K19|]. split; [exact K26|]. split; [exact K27|].
              rewrite (proj2 (Z.eqb_neq (g_n g - 6) 0) Hwn) in K22, K25.
              split; [transitivity (Z_to_bv 64 (g_p g + 6 + 1)); [exact K22 | f_equal; r1_lia]|].
              split; [transitivity (Z_to_bv 64 (g_n g - 6 - 1)); [exact K25 | f_equal; r1_lia]|].
              split; [exact MU1|]. split; [exact WM1 | exact HB1].
           ++ (* odd mode: spills, the count cell's shadow byte, the count cell and the call *)
              subst ms2.
              eapply evt_cut.
              { apply r1_spill_evt with (A := A) (fr := fr) (Sh := Sfr fr) (spv := sp)
                  (x48 := x48) (x56 := x56) (x72 := x72) (x80 := x80) (x88 := x88) (x128 := x128)
                  (sh1 := sh1) (cs := cs); r1_side. }
              intros ms3 (m2 & E3 & MUs & WMs & ACs & SWs & STAs & STs & CHsh2 & CHc2 & H48s & H128s &
                          H56s & H72s & H80s & H88s).
              subst ms3.
              eapply evt_cut.
              { apply r1_shadow_evt with (A := A) (fr := fr) (Sh := Sfr fr) (spv := sp) (sh1 := sh1) (cs := cs);
                  r1_side. }
              intros ms4 (m3 & E4 & MUh & WMh & ACh & SWh & STAh & STh & CHc3 & HSHh & H48h & H128h).
              subst ms4.
              eapply evt_mono.
              { apply (r1_call_evt CATC) with (A := A) (fr := fr) (Sh := Sfr fr) (spv := sp) (cs := cs);
                  r1_side. }
              intros ms5 (R & m4 & E6 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K25 & K26 & K10 &
                          MUc & WMc & SWc & STAc & STc & HZc & HZ48 & HZ128).
              subst ms5.
              (* the four spills of 0x814d0 .. 0x814dc survive the shadow store and the catalogue call *)
              assert (TR : forall a (vv : word), bytes_at rsegs m2 a (le8 vv) -> A + 48 <= a -> a + 8 <= A + 136 ->
                             bytes_at rsegs m4 a (le8 vv)).
              { intros a vv Hb Ha1 Ha2. destruct HShA as (HsA0 & HsP0).
                apply (bytes_at_transport rsegs _ m3 m4 _ _
                         (bytes_at_transport rsegs _ m2 m3 _ _ Hb MUh
                            ltac:(rewrite length_le8; cbn [disjoint_from]; split; [r1_lia | exact I])) MUc).
                rewrite length_le8. cbn [disjoint_from]. repeat split; first [exact I | r1_lia]. }
              exists R, (Z_to_bv 64 0x814f8), m4. split; [reflexivity|].
              right; right. exists m2, m3.
              split; [reflexivity|]. split; [exact E5|]. split; [r1_lia|].
              split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|].
              split; [exact K9|]. split; [exact K19|]. split; [exact K26|].
              split; [exact K18|]. split; [exact K21|]. split; [exact K10|].
              split; [transitivity (Z_to_bv 64 (g_p g + 6 + 1)); [exact K22 | f_equal; r1_lia]|].
              split; [transitivity (Z_to_bv 64 (g_n g - 6 - 1)); [exact K25 | f_equal; r1_lia]|].
              split.
              { transitivity (zxb (RcIdentModel.nthb (g_in g) 6%nat)); [exact K23|]. unfold SlotModel.mode.
                change (SlotModel.nlen (g_in g)) with (g_n g).
                replace (7 <=? g_n g) with true by (symmetry; apply Z.leb_le; r1_lia).
                reflexivity. }
              split.
              { apply (munch_trans W1 mem m1 m2).
                - apply (munch_weaken Wf); [unfold Wf, W1; intros x Hx; cbn [LF.outside] in Hx |- *; clear - Hx; tauto
                                           | exact MU1].
                - apply (munch_weaken [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)]);
                    [unfold W1; intros x Hx; cbn [LF.outside] in Hx |- *; clear - Hx; tauto | exact MUs]. }
              split; [exact (wmono_trans rsegs mem m1 m2 WM1 WMs)|].
              split.
              { apply (bytes_at_transport rsegs _ m1 m2 _ _ HOUR1 MUs).
                rewrite OUR_length. cbn [disjoint_from]. repeat split; (exact I || r1_lia). }
              split; [exact STAs|].
              split; [exact MUh|]. split; [exact WMh|]. split; [exact SWh|]. split; [exact HSHh|].
              split; [exact MUc|]. split; [exact WMc|]. split; [exact STc|].
              split; [exact HZc|]. split; [exact HZ48|]. split; [exact HZ128|].
              split; [exact (TR _ _ H56s ltac:(r1_lia) ltac:(r1_lia))|].
              split; [exact (TR _ _ H72s ltac:(r1_lia) ltac:(r1_lia))|].
              split; [exact (TR _ _ H80s ltac:(r1_lia) ltac:(r1_lia))|].
              exact (TR _ _ H88s ltac:(r1_lia) ltac:(r1_lia)).
      * (* back edge to turn t + 1 *)
        eapply evt_mono.
        -- apply r1_ld_evt with (ou := fr + 2624) (t := t) (K := ASAN_K) (A := A) (q := g_p g + t)
             (v := g_n g - t) (b := RcIdentModel.nthb (g_in g) (Z.to_nat t)) (kq := kq) (kd := Z_to_bv 8 6);
             r1_side.
        -- intros ms' (y5 & y6 & y7 & m' & Ems & MU & WM & HB).
           rewrite (proj2 (Z.eqb_neq t 5) N5) in Ems. cbv iota in Ems. subst ms'.
           do 3 eexists. split; [reflexivity|].
           left. exists (RcIdentModel.nthb (g_in g) (Z.to_nat t)).
           split; [reflexivity|]. split; [r1_lia|]. split; [reflexivity|].
           do 18 (split; [reflexivity|]).
           split; [r1_gz (Z_to_bv 64 (fr + 2624 + t + 1))|].
           split; [r1_gz (Z_to_bv 64 (t + 2))|].
           split; [r1_gz (Z_to_bv 64 (fr + 2624 + t + 1))|].
           split; [r1_gz (Z_to_bv 64 (g_p g + t + 1))|].
           split; [r1_gz (Z_to_bv 64 (g_n g - t - 1))|].
           split; [exact MU|]. split; [exact WM | exact HB].
    + (* left = 0: our[t] = 0 *)
      assert (Hmin : Z.min t (g_n g) = g_n g) by r1_lia.
      rewrite Hmin in Hg22, Hg25.
      replace (g_n g - g_n g) with 0 in Hg25 by r1_lia.
      assert (Hv0 : RcIdentModel.nthb (g_in g) (Z.to_nat t) = Z_to_bv 8 0) by (apply r1_nth_past; r1_lia).
      destruct (Z.eq_dec t 5) as [E5 | N5].
      * (* turn 5, left = 0: the 0x81440 arm to P3 *)
        eapply evt_mono.
        -- apply r1_z_evt with (d := fr + 2624 + t) (K := ASAN_K) (l := t + 1) (r := t) (kb := Z_to_bv 8 6);
             r1_side.
        -- intros ms' (y5 & y6 & m' & Ems & MU & WM & HB).
           rewrite (proj2 (Z.eqb_eq (t + 1) 6) ltac:(r1_lia)) in Ems. subst ms'.
           do 3 eexists. split; [reflexivity|].
           right; left. exists (Z_to_bv 8 0).
           split; [reflexivity|]. split; [exact E5|]. split; [symmetry; exact Hv0|].
           do 8 (split; [reflexivity|]).
           split; [transitivity (getr regs 22); [reflexivity | etransitivity; [exact Hg22 | f_equal; r1_lia]]|].
           split; [r1_gz (Z_to_bv 64 0)|].
           split; [exact MU|]. split; [exact WM | exact HB].
      * (* back edge to turn t + 1 *)
        eapply evt_mono.
        -- apply r1_z_evt with (d := fr + 2624 + t) (K := ASAN_K) (l := t + 1) (r := t) (kb := Z_to_bv 8 6);
             r1_side.
        -- intros ms' (y5 & y6 & m' & Ems & MU & WM & HB).
           rewrite (proj2 (Z.eqb_neq (t + 1) 6) ltac:(r1_lia)) in Ems. subst ms'.
           do 3 eexists. split; [reflexivity|].
           left. exists (Z_to_bv 8 0).
           split; [reflexivity|]. split; [r1_lia|]. split; [symmetry; exact Hv0|].
           do 18 (split; [reflexivity|]).
           split; [r1_gz (Z_to_bv 64 (fr + 2624 + t + 1))|].
           split; [r1_gz (Z_to_bv 64 (t + 1 + 1))|].
           split; [r1_gz (Z_to_bv 64 (fr + 2624 + t + 1))|].
           split; [transitivity (getr regs 22); [reflexivity | etransitivity; [exact Hg22 | f_equal; r1_lia]]|].
           split; [r1_gz (Z_to_bv 64 0)|].
           split; [exact MU|]. split; [exact WM | exact HB].
  - intros R pc' mem' regs'' md'
      [ (v & Hpc & Ht5 & Hv & K1 & K2 & K3 & K4 & K7 & K8 & K9 & K12 & K13 & K18 & K19 & K21 & K26 & K27 & K28 &
           K29 & K30 & K31 & K10 & K11 & K14 & K22 & K25 & MU & WM & HB)
      | [ (v & Hpc & Ht5 & Hv & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25 & MU & WM & HB)
        | (ma & mb & Hpc & Ht5 & Hn7 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K18 & K21 & K10 & K22 & K25 & K23 &
           MU1 & WM1 & HOURa & STAa & MU2 & WM2 & HSWb & HSHb & MU3 & WM3 & STw & HZc & HZ48 &
           HZ128 & HZ56 & HZ72 & HZ80 & HZ88) ] ]
      Hreg Hmat; subst pc'.
    + exact (NEXT v R mem' regs'' md' Ht5 Hv K1 K2 K3 K4 K7 K8 K9 K12 K13 K18 K19 K21 K26 K27 K28 K29 K30 K31
               K10 K11 K14 K22 K25 MU WM HB Hreg Hmat).
    + exact (EXITP3 v R mem' regs'' md' Ht5 Hv K2 K3 K4 K8 K9 K19 K26 K27 K22 K25 MU WM HB Hreg Hmat).
    + exact (EXITR2 R ma mb mem' regs'' md' Ht5 Hn7 K2 K3 K4 K8 K9 K19 K26 K18 K21 K10 K22 K25 K23
               MU1 WM1 HOURa STAa MU2 WM2 HSWb HSHb MU3 WM3 STw HZc HZ48 HZ128 HZ56 HZ72 HZ80 HZ88 Hreg Hmat).
Qed.

(* S_R1: the our[] loop is closed by induction on 5 - t, inside the lemma. *)
Lemma seg_R1 : Hcut B APIf ra (Inv_A814f8 B APIf ra) -> Hcut B APIf ra (Inv_A81b14 B APIf ra) ->
  Hcut B APIf ra (Inv_A81414 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros HR2 HP3.
  assert (MAIN : forall (k : nat) t, Z.to_nat (5 - t) = k -> Hat B APIf ra (Inv_A81414_at B APIf ra) t).
  { induction k as [|k IH]; intros t' Ek; apply r1_turn; try exact HP3; try exact HR2.
    - intros Hlt. exfalso. lia.
    - intros Hlt. apply IH. lia. }
  intros g c (t & Hc). exact (MAIN (Z.to_nat (5 - t)) t eq_refl g c Hc).
Qed.


End R1.
