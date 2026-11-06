From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import printf_facts_c snprintf_c reac_rate_drivable_csv_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** General lemmas for the walk of reac_rate_drivable_csv in the UBSan image (dcsv_*.v). The ones marked "from"
    are copies of released lemmas with this tree's module paths. *)

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/disco_table.v:112-118 *)
Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma ltz_lit : forall a, 0 <= a < 2^63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof. intros a Ha. rewrite bv_lts_zero_r, unsigned_lit by lia. apply Z.leb_gt. lia. Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:221-229 *)
Lemma task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview rsegs m a <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TK MU HW a b E. destruct (m a) as [b0|] eqn:E0; [exact (TK a b0 E0)|].
  assert (HI : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho), E0 in E; discriminate).
  pose proof (HW a HI) as W0. unfold wview in W0. rewrite E0 in W0.
  destruct (find_segment rsegs (bv_unsigned a) 1) eqn:EF; [left; discriminate|].
  exfalso. apply W0. reflexivity.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:147-171 *)
Lemma bytes_at_mrd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (Ha & Hl & H) Hx.
  replace x with (A + Z.of_nat (Z.to_nat (x - A))) by lia. rewrite H by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hc a Ha) as [Ho | Hb'].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exact Hb'.
Qed.

Lemma stk_cb : forall m A n, stk rsegs m A (A + Z.of_nat n) -> exists j, rw_cells rsegs m A [CB n j].
Proof.
  intros m A n H. pose proof H as (H1 & _ & _).
  destruct (stk_carve rsegs m A (A + Z.of_nat n) n H ltac:(lia)) as [_ (j & J)].
  exists j. replace (A + Z.of_nat n - Z.of_nat n) with A in J by lia. exact J.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:269-290 *)
Lemma rwc_stk : forall m A n j, rw_cells rsegs m A [CB n j] -> stk rsegs m A (A + Z.of_nat n).
Proof.
  intros m A n j [[[Lj _] B] (H1 & H2 & HW)]. cbn [cells_size csize cells_bytes cbytes] in *.
  rewrite app_nil_r in B. rewrite Nat.add_0_r in *.
  split; [lia|]. split; [lia|]. intros a Ha. split.
  - replace a with (A + (a - A)) by lia. apply HW. lia.
  - eapply bytes_at_mrd; [exact B|]. rewrite Lj. lia.
Qed.

Lemma stk_sub : forall m a b a' b', stk rsegs m a b -> a <= a' -> a' <= b' -> b' <= b -> stk rsegs m a' b'.
Proof.
  intros m a b a' b' (H1 & H2 & H) X1 X2 X3. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

Lemma rwc_cb : forall m A n j, rw_cells rsegs m A [CB n j] -> length j = n /\ bytes_at rsegs m A j.
Proof. intros m A n j [[[Lj _] B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. split; assumption. Qed.

(** A [CB] cell of n bytes inside a writable, readable stretch. *)
Lemma stk_cb_at : forall m lo hi A n, stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists j, rw_cells rsegs m A [CB n j].
Proof. intros m lo hi A n H H1 H2. apply stk_cb. eapply stk_sub; [exact H | lia | lia | lia]. Qed.

(** The stack is outside every reserved image segment: they all end at or below 0x51000. *)
Lemma dcsv_img_free : forall D n, 0x51000 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs.
  assert (H : forallb (fun s : word * word => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x51000)
                (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hs). apply Z.leb_le in H. lia.
Qed.

(** Every address of a stretch the stack predicate covers has a writable view. *)
Lemma stk_wview : forall m lo hi (a : word), stk rsegs m lo hi -> lo <= bv_unsigned a < hi -> wview rsegs m a <> None.
Proof.
  intros m lo hi a (_ & _ & H) Ha. destruct (H _ Ha) as [W _]. unfold wa in W. rewrite Z_to_bv_lit_self in W. exact W.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:126-145 *)
Lemma rw_cells_app : forall m A c1 c2,
  rw_cells rsegs m A (c1 ++ c2) <-> rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2.
Proof.
  intros m A c1 c2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (Ha & Hl & Hw)].
    rewrite cells_bytes_length in B2 by exact W1.
    split; split; try (split; assumption).
    + split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size c1) + i) with (A + (Z.of_nat (cells_size c1) + i)) by lia. apply Hw. lia.
  - intros [[[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)]].
    rewrite cells_bytes_length by exact W1.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size c1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size c1) + (i - Z.of_nat (cells_size c1))) by lia. apply Hw2. lia.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:173-177 *)
Lemma pf_bytes_app : forall a b, pf_bytes (a ++ b) = pf_bytes a ++ pf_bytes b.
Proof. intros. unfold pf_bytes. apply map_app. Qed.

Lemma length_pf_bytes : forall a, length (pf_bytes a) = length a.
Proof. intros. unfold pf_bytes. apply length_map. Qed.

(** The format string "%s%d" at FMT_SD (0x10470, .rodata). *)
Lemma dcsv_fmt : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10470 (pf_bytes ([37; 115; 37; 100] ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:673-685, with the bounds as parameters *)
Lemma dcsv_str : forall m S lo D n (A : Z) (s sl : list Z),
  mem_inv rsegs m -> ro_bytes_b rsegs A (pf_bytes (s ++ [0] ++ sl)) = true ->
  Forall (fun c => 0 < c < 256) s ->
  (- (A + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length sl) ->
  0 < A -> A + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= lo ->
  A + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= D ->
  A + Z.of_nat (length s) + 1 + Z.of_nat (length sl) < 2^63 ->
  pf_arg_ok m S lo D n (Z_to_bv 64 A) (APtr s).
Proof.
  intros m S lo D n A s sl MI RB FA HM HA HL HD H63. cbn [pf_arg_ok]. rewrite (unsigned_lit A) by lia.
  split; [exact FA|]. exists (pf_bytes sl). rewrite length_pf_bytes.
  split; [|split; [lia|split; [lia|split; lia]]].
  rewrite <- pf_bytes_app, <- app_assoc. apply ro_bytes_at; [exact MI | lia | | apply ro_bytes_b_sound; exact RB].
  rewrite length_pf_bytes, !length_app. cbn [length]. lia.
Qed.

(** The separators: "" at STR_EMPTY (0x1032e; slack byte 0x1032f = '4') and "," at STR_COMMA (0x10373; slack
    0x10375 .. 0x10377 = "not", the start of "not_drivable"). *)
Lemma dcsv_s_empty : forall m S lo D n, mem_inv rsegs m -> 0x10330 <= lo -> 0x10330 <= D ->
  pf_arg_ok m S lo D n (Z_to_bv 64 0x1032e) (APtr []).
Proof.
  intros m S lo D n MI HL HD. eapply (dcsv_str m S lo D n _ [] [52] MI);
    [vm_compute; reflexivity | constructor | cbn; lia | lia | cbn; lia | cbn; lia | cbn; lia].
Qed.

Lemma dcsv_s_comma : forall m S lo D n, mem_inv rsegs m -> 0x10378 <= lo -> 0x10378 <= D ->
  pf_arg_ok m S lo D n (Z_to_bv 64 0x10373) (APtr [44]).
Proof.
  intros m S lo D n MI HL HD. eapply (dcsv_str m S lo D n _ [44] [110; 111; 116] MI);
    [vm_compute; reflexivity | repeat constructor; lia | cbn; lia | lia | cbn; lia | cbn; lia | cbn; lia].
Qed.

(** The separator the code passes as a3 (`mv a3,s7`, and `mv a3,s11` when len <> 0; 0x14e90 .. 0x14e98), as the
    contract review read it. *)
Definition sep_of (len : Z) : Z := if len =? 0 then 0x1032e else 0x10373.
Definition sep_str (len : Z) : list Z := if len =? 0 then [] else [44].

Lemma dcsv_s_sep : forall len m S lo D n, mem_inv rsegs m -> 0x10378 <= lo -> 0x10378 <= D ->
  pf_arg_ok m S lo D n (Z_to_bv 64 (sep_of len)) (APtr (sep_str len)).
Proof.
  intros len m S lo D n MI HL HD. unfold sep_of, sep_str.
  destruct (len =? 0); [apply dcsv_s_empty | apply dcsv_s_comma]; first [exact MI | lia].
Qed.

Lemma sep_str_len : forall len, (length (sep_str len) <= 1)%nat.
Proof. intros len. unfold sep_str. destruct (len =? 0); cbn; lia. Qed.

Lemma sep_str_prefix : forall (P : list Z), sep_str (Z.of_nat (length P)) = match P with [] => [] | _ :: _ => [44] end.
Proof. intros [|c P]; [reflexivity|]. unfold sep_str. cbn [length]. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

(** "%s%d" with [APtr sep; AInt rate] writes sep ++ "%d" of rate. *)
Lemma dcsv_text : forall sep rate, pf_text [Ps; Pd] [APtr sep; AInt rate] = Some (sep ++ csv_dec rate).
Proof. intros sep rate. cbn. rewrite app_nil_r, pf_dec_csv. reflexivity. Qed.

(** The three rates: their "%d" text has 5 bytes, each a digit. *)
Lemma dcsv_rate_len : forall i, (i < 3)%nat -> length (csv_dec (nth i closed_list 0)) = 5%nat.
Proof. intros i Hi. destruct i as [|[|[|i]]]; [reflexivity | reflexivity | reflexivity | lia]. Qed.

Lemma dcsv_rate_range : forall i, (i < 3)%nat -> 44100 <= nth i closed_list 0 <= 96000.
Proof.
  intros i Hi. destruct i as [|[|[|i]]];
    [change (nth 0 closed_list 0) with 44100 | change (nth 1 closed_list 0) with 48000
    | change (nth 2 closed_list 0) with 96000 | ]; lia.
Qed.

Lemma dcsv_bit_range : forall i, (i < 3)%nat -> 1 <= rate_bit (nth i closed_list 0) <= 4.
Proof.
  intros i Hi. destruct i as [|[|[|i]]];
    [change (rate_bit (nth 0 closed_list 0)) with 1 | change (rate_bit (nth 1 closed_list 0)) with 2
    | change (rate_bit (nth 2 closed_list 0)) with 4 | ]; lia.
Qed.

Lemma dcsv_land_range : forall b x, 0 <= b < 2^64 -> 0 <= x -> 0 <= Z.land b x < 2^64.
Proof. intros b x Hb Hx. exact (zr_land_l b x Hb Hx). Qed.

(** Transport across a callee's or a store's footprint, address by address. *)
Lemma bytes_at_tr : forall W m m' A bs, bytes_at rsegs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - rewrite wa_unsigned by lia. apply Hd. lia.
Qed.

Lemma rw_cells_tr : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
  - eapply bytes_at_tr; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[a b] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec a x) as [H1|H1]; [destruct (Z_lt_dec x b) as [H2|H2]|].
  - right. intros [H3 _]. apply H3. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Lemma outside_of : forall W (R : Z -> Prop) x, (forall y, ~ outside W y -> R y) -> ~ R x -> outside W x.
Proof. intros W R x H HR. destruct (outside_dec W x) as [O|O]; [exact O|]. exfalso. apply HR, H, O. Qed.

(** task_mem after the walk's writes, from task_mem at entry (as tj_lemmas.v:400-406 tj_task). *)
Lemma dcsv_task : forall m0 m lo S0, MemNorm.task_mem rsegs m0 -> stk rsegs m0 lo S0 -> munch [(lo, S0)] m0 m ->
  MemNorm.task_mem rsegs m.
Proof.
  intros m0 m lo S0 TK ST MU. eapply task_mem_munch; [exact TK | exact MU |]. intros a HI.
  eapply stk_wview; [exact ST |]. cbn [outside] in HI. lia.
Qed.

Lemma dcsv_task2 : forall m0 m lo S0 buf n junk, MemNorm.task_mem rsegs m0 -> stk rsegs m0 lo S0 ->
  rw_cells rsegs m0 buf [CB (Z.to_nat n) junk] -> 0 <= n -> munch [(lo, S0); (buf, buf + n)] m0 m ->
  MemNorm.task_mem rsegs m.
Proof.
  intros m0 m lo S0 buf n junk TK ST RB Hn MU. eapply task_mem_munch; [exact TK | exact MU |]. intros a HI.
  assert (HR : lo <= bv_unsigned a < S0 \/ buf <= bv_unsigned a < buf + n) by (cbn [outside] in HI; lia).
  destruct HR as [HR|HR]; [eapply stk_wview; [exact ST | exact HR]|].
  pose proof (rwc_stk _ _ _ _ RB) as SB. rewrite Z2Nat.id in SB by lia. eapply stk_wview; [exact SB | exact HR].
Qed.

(** drivable_csv's snprintf call (0x14ea8): snprintf(cell = sp + 0x18, 16, "%s%d", sep, rate) with sp = S0 - 176.
    Premise discharge as in the contract review's dcsv_snprintf_call, here with the post: snprintf leaves
    T = sep ++ "%d" of rate (at most 6 bytes, so the 16-byte cell holds all of it) and a NUL at the cell. *)
Lemma dcsv_snp : snprintf_contract ->
  forall (m : word -> option byte) (lo S0 len : Z) (i : nat) (fc : bv 32) (canary : word) (F : bvmap 5 word)
         ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  stk rsegs m lo (S0 + -176) -> stk rsegs m (S0 + -152) (S0 + -136) -> lo + 6112 <= S0 -> 0x50cc8 <= lo ->
  S0 < 2^63 -> bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc -> (i < 3)%nat ->
  evt rsegs (printf_post ra (Z_to_bv 64 (S0 + -176)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (S0 + -152)
               (Z.of_nat (length (sep_str len ++ csv_dec (nth i closed_list 0))))
               (sep_str len ++ csv_dec (nth i closed_list 0)) m)
    (MS (mkR ra (Z_to_bv 64 (S0 + -176)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S0 + -152)) (Z_to_bv 64 16)
             (Z_to_bv 64 0x10470) (Z_to_bv 64 (sep_of len)) (Z_to_bv 64 (nth i closed_list 0)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18c90) fc None m (seg_rom rsegs)).
Proof.
  intros SNP m lo S0 len i fc canary F ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ST SC HK HI H63 GG GD MI TK FC Hi.
  pose proof ST as (Hlo & _ & _).
  pose proof (dcsv_rate_range i Hi) as RR. pose proof (dcsv_rate_len i Hi) as RL. pose proof (sep_str_len len) as SL.
  destruct (stk_cb_at m (S0 + -152) (S0 + -136) (S0 + -152) 16 SC ltac:(lia) ltac:(lia)) as [jc RC].
  pose proof (SNP ra (Z_to_bv 64 (S0 + -176)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S0 + -152)) (Z_to_bv 64 16)
                (Z_to_bv 64 0x10470) (Z_to_bv 64 (sep_of len)) (Z_to_bv 64 (nth i closed_list 0)) a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary [37; 115; 37; 100] [Ps; Pd]
                [APtr (sep_str len); AInt (nth i closed_list 0)] (sep_str len ++ csv_dec (nth i closed_list 0)) jc)
    as H.
  cbv zeta in H.
  rewrite (unsigned_lit (S0 + -176)), (unsigned_lit (S0 + -152)), (unsigned_lit 16), (unsigned_lit 0x10470) in H
    by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in H.
  rewrite firstn_all2 in H by (rewrite length_app, RL; lia).
  apply H; clear H.
  - apply dcsv_fmt. exact MI.
  - unfold RO_LO. lia.
  - unfold RO_END. cbn [length]. lia.
  - reflexivity.
  - cbn [pf_args_ok]. split; [apply dcsv_s_sep; [exact MI | lia | lia]|]. split; [|exact I].
    cbn [pf_arg_ok]. rewrite unsigned_lit by lia. split; [lia | reflexivity].
  - apply dcsv_text.
  - exact RC.
  - lia.
  - rewrite length_app, RL. lia.
  - lia.
  - right. lia.
  - apply dcsv_img_free. lia.
  - exact ST.
  - unfold SNPRINTF_K. lia.
  - unfold IMG_END. lia.
  - lia.
  - exact FC.
  - exact MI.
  - exact TK.
  - exact GG.
  - exact GD.
Qed.

(** The `sb zero` store as one byte (from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/slot_R0_R3.v:77-82). *)
Ltac fix_zero_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 0))) _) =>
      change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; mem_after_store
  end.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:719-724 *)
Ltac run_to pc :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_true | if_false]
  end.
