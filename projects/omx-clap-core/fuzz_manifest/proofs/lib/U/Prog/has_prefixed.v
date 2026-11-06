From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem LibcNeeds_c has_prefixed_c has_prefixed_model.
Import ListNotations.
Open Scope Z_scope.

Lemma lts_small : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma eqb_small : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma firstn1_skipn : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma rd_text : forall m T (tb ts : list byte) (k : nat),
  bytes_at rsegs m T (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  ov_read_bytes rsegs m (wa (T + Z.of_nat k)) 1 = Some [nth k (tb ++ Z_to_bv 8 0 :: ts) (Z_to_bv 8 0)].
Proof.
  intros m T tb ts k H Hk.
  rewrite (bytes_at_read rsegs m T _ (Z.of_nat k) 1 H) by (try lia; rewrite length_app; cbn [length]; lia).
  rewrite Nat2Z.id. f_equal. apply firstn1_skipn. rewrite length_app. cbn [length]. lia.
Qed.

Lemma bytes_at_suffix : forall m T (tb ts : list byte) (k : nat),
  bytes_at rsegs m T (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  bytes_at rsegs m (T + Z.of_nat k) (skipn k tb ++ Z_to_bv 8 0 :: ts).
Proof.
  intros m T tb ts k H Hk. rewrite <- (firstn_skipn k tb) in H. rewrite <- app_assoc in H.
  apply bytes_at_app in H as [_ H]. rewrite length_firstn in H. replace (Nat.min k (length tb)) with k in H by lia.
  exact H.
Qed.

Lemma cstr_suffix : forall m T (tb ts : list byte) (k : nat),
  bytes_at rsegs m T (tb ++ Z_to_bv 8 0 :: ts) -> Forall (fun b => bv_unsigned b <> 0) tb ->
  (- (T + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length ts) -> (k <= length tb)%nat ->
  cstr_at m (T + Z.of_nat k) (skipn k tb) ts.
Proof.
  intros m T tb ts k H NZ SL Hk. split; [apply bytes_at_suffix; assumption|]. split.
  - rewrite <- (firstn_skipn k tb) in NZ. apply Forall_app in NZ as [_ NZ]. exact NZ.
  - rewrite length_skipn. replace (T + Z.of_nat k + Z.of_nat (length tb - k)) with (T + Z.of_nat (length tb)) by lia.
    exact SL.
Qed.

Lemma cstr0_suffix : forall m T (tb ts : list byte) (k : nat),
  bytes_at rsegs m T (tb ++ Z_to_bv 8 0 :: ts) -> Forall (fun b => bv_unsigned b <> 0) tb -> (k <= length tb)%nat ->
  cstr0 m (T + Z.of_nat k) (skipn k tb).
Proof.
  intros m T tb ts k H NZ Hk. split.
  - pose proof (bytes_at_suffix m T tb ts k H Hk) as H2.
    replace (skipn k tb ++ Z_to_bv 8 0 :: ts) with ((skipn k tb ++ [Z_to_bv 8 0]) ++ ts) in H2
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in H2 as [H2 _]. exact H2.
  - rewrite <- (firstn_skipn k tb) in NZ. apply Forall_app in NZ as [_ NZ]. exact NZ.
Qed.

Lemma isal_true : forall (r : word) b, (bv_unsigned r <> 0 <-> b = true) -> b = true -> bv_unsigned r <> 0.
Proof. intros r b H E. apply H. exact E. Qed.

Lemma isal_false : forall (r : word) b, (bv_unsigned r <> 0 <-> b = true) -> b = false -> bv_unsigned r = 0.
Proof.
  intros r b H E. destruct (Z.eq_dec (bv_unsigned r) 0) as [Z0|Z0]; [exact Z0|]. apply H in Z0. congruence.
Qed.

Lemma land1_range : forall x, 0 <= Z.land x 1 <= 1.
Proof.
  intros x. replace (Z.land x 1) with (x mod 2) by (symmetry; apply (Z.land_ones x 1); lia).
  pose proof (Z.mod_pos_bound x 2). lia.
Qed.

Lemma in_bytes : forall c, 0 <= c < 256 -> In c (map Z.of_nat (seq 0 256)).
Proof. intros c Hc. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. Qed.

Lemma nc_parts : forall c, 0 <= c < 256 -> is_alnum c = false ->
  name_char c = (negb (58 mod 2^64 <? (c + -37) mod 2^64)
                 && negb (Z.land (324259173172773121 ≫ ((c + -37) mod 64)) 1 =? 0)) || (128 <=? c).
Proof.
  intros c Hc HA.
  assert (G : forallb (fun x => implb (negb (is_alnum x)) (Bool.eqb (name_char x)
                ((negb (58 mod 2^64 <? (x + -37) mod 2^64)
                  && negb (Z.land (324259173172773121 ≫ ((x + -37) mod 64)) 1 =? 0)) || (128 <=? x))))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in G. specialize (G c (in_bytes c Hc)). rewrite HA in G. cbn [negb implb] in G.
  apply Bool.eqb_prop. exact G.
Qed.

Lemma sx_sign : forall c, 0 <= c < 256 ->
  bv_lts (Z_to_bv 64 (bv_signed (Z_to_bv 64 (c ≪ 56)) ≫ 56)) (Z_to_bv 64 0) = (128 <=? c).
Proof.
  intros c Hc.
  assert (G : forallb (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (bv_signed (Z_to_bv 64 (x ≪ 56)) ≫ 56)) (Z_to_bv 64 0))
                                         (128 <=? x)) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in G. apply Bool.eqb_prop. exact (G c (in_bytes c Hc)).
Qed.

Lemma sl_sign : forall c, 0 <= c < 256 -> bv_lts (Z_to_bv 64 (c ≪ 56)) (Z_to_bv 64 0) = (128 <=? c).
Proof.
  intros c Hc.
  assert (G : forallb (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (x ≪ 56)) (Z_to_bv 64 0)) (128 <=? x))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in G. apply Bool.eqb_prop. exact (G c (in_bytes c Hc)).
Qed.

Ltac cnd :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); cnd
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); cnd
  | |- _ => first [ reflexivity | apply Z.ltb_lt; mlia | apply Z.ltb_ge; mlia | apply Z.eqb_eq; mlia
                  | apply Z.eqb_neq; mlia ]
  end.

Ltac nt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota | symmetry; unfold bv_ltu, bv_eqb, bv_lts; cbn [negb]; rewrite ?unsigned_lit_wrap;
                  rewrite ?zb_lxor_ones by lia; cnd]
  end.

Lemma frame_merge : forall m A mid post,
  rw_cells rsegs m A (mid ++ post) -> rw_cells rsegs m A (CB (cells_size mid) (cells_bytes mid) :: post).
Proof. intros m A mid post H. exact (rw_cells_merge rsegs m A [] mid post H). Qed.

Section HpLoop.
Hypothesis STRSTR : strstr_contract.
Hypothesis STRNCMP : strncmp_contract.
Hypothesis ISALNUM : isalnum_contract.
Variables (Q : machine_state -> Prop) (sq gp tp lw plw pw tw : word) (F : bvmap 5 word) (fc : bv 32)
  (lo q : Z) (tb ts lb ls : list byte) (fj : list byte) (rest : list cell).
Hypothesis HLN : lb <> [].
Hypothesis HTX : 4096 <= bv_unsigned tw.
Hypothesis HTN : Z.of_nat (length tb) + 1 < 2^63.
Hypothesis HQ : 0 <= q.
Hypothesis HQP : q + bv_unsigned plw <= Z.of_nat (length tb).
Hypothesis HPRE : bv_unsigned pw = bv_unsigned tw + q.
Hypothesis TNZ : Forall (fun b => bv_unsigned b <> 0) tb.
Hypothesis TSL : (- (bv_unsigned tw + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length ts).
Hypothesis LNZ : Forall (fun b => bv_unsigned b <> 0) lb.
Hypothesis LSL : (- (bv_unsigned lw + Z.of_nat (length lb) + 1)) mod 8 <= Z.of_nat (length ls).
Hypothesis LO : lo + 2256 <= bv_unsigned sq.
Hypothesis DT : off_stack sq 2256 (bv_unsigned tw) (Z.of_nat (length tb + 1 + length ts)).
Hypothesis DL : off_stack sq 2256 (bv_unsigned lw) (Z.of_nat (length lb + 1 + length ls)).
Variable g : word.
Hypothesis GB1 : 0x4f978 + 8 <= bv_unsigned sq - 2256.
Hypothesis GB2 : 0x1e368 + 8 <= bv_unsigned sq - 2256.

Local Abbreviation PRE := (firstn (Z.to_nat (bv_unsigned plw)) (skipn (Z.to_nat q) (zbytes tb))).
Local Abbreviation FRC :=
  (CB 8 fj :: C8 (Z_to_bv 64 324259173172773121) :: C8 (Z_to_bv 64 (Z.of_nat (length lb))) :: rest).

Lemma hp_loop : forall (n a : nat) (m : word -> option byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
  (length tb - a < n)%nat ->
  bytes_at rsegs m (bv_unsigned tw) (tb ++ Z_to_bv 8 0 :: ts) ->
  bytes_at rsegs m (bv_unsigned lw) (lb ++ Z_to_bv 8 0 :: ls) ->
  bytes_at rsegs m 0x1e368 (le8 (Z_to_bv 64 0x4f978)) -> bytes_at rsegs m 0x4f978 (le8 g) ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sq) -> rw_cells rsegs m (bv_unsigned sq) FRC ->
  mt (zbytes tb) (zbytes lb) a = true ->
  (forall j, (j + length PRE + 1 < a)%nat -> token_at (zbytes tb) PRE (zbytes lb) j = false) ->
  (forall (m' : word -> option byte) (r : Z) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
            x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
     munch [(bv_unsigned sq - 2256, bv_unsigned sq)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sq) -> rw_cells rsegs m' (bv_unsigned sq) FRC ->
     r = (if token (zbytes tb) PRE (zbytes lb) then 1 else 0) ->
     evt rsegs Q (MS (mkR x1 sq gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                          x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14384) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sq gp tp t0 t1 t2 lw plw a0 a1 a2 a3 a4 a5 a6 a7 pw tw s4
             (Z_to_bv 64 (bv_unsigned tw + Z.of_nat a)) s6 (Z_to_bv 64 (bv_unsigned plw + 1))
             (Z_to_bv 64 (- bv_unsigned plw)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1) (Z_to_bv 64 58) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1429c) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH];
    intros a m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 HN HTb HLb GC GW MI ST FRM MT INV CONT; [lia|].
  pose proof (bytes_at_bound _ _ _ _ HTb) as BT. pose proof (bytes_at_bound _ _ _ _ HLb) as BL.
  rewrite length_app in BT, BL. cbn [length] in BT, BL.
  pose proof (mt_len _ _ _ MT) as MTL. rewrite !length_zbytes in MTL.
  assert (LBP : (1 <= length lb)%nat) by (destruct lb; [contradiction|cbn; lia]).
  assert (LPRE : length PRE = Z.to_nat (bv_unsigned plw)).
  { rewrite length_firstn, length_skipn, length_zbytes. lia. }
  pose proof (bv_unsigned_in_range 64 tw) as Rtw. pose proof (bv_unsigned_in_range 64 plw) as Rpl.
  pose proof (bv_unsigned_in_range 64 lw) as Rlw. pose proof (bv_unsigned_in_range 64 sq) as Rsq.
  pose proof (bv_unsigned_in_range 64 pw) as Rpw.
  unfold bv_modulus in Rtw, Rpl, Rlw, Rsq, Rpw.
  pose proof DT as DT'. pose proof DL as DL'. unfold off_stack in DT', DL'.
  assert (CONTINUE : forall (m1 : word -> option byte)
            (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 : word),
    munch [(bv_unsigned sq - 2256, bv_unsigned sq)] m m1 -> wmono rsegs m m1 ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sq) -> rw_cells rsegs m1 (bv_unsigned sq) FRC ->
    bytes_at rsegs m1 (bv_unsigned tw) (tb ++ Z_to_bv 8 0 :: ts) ->
    bytes_at rsegs m1 (bv_unsigned lw) (lb ++ Z_to_bv 8 0 :: ls) ->
    bytes_at rsegs m1 0x1e368 (le8 (Z_to_bv 64 0x4f978)) -> bytes_at rsegs m1 0x4f978 (le8 g) ->
    (forall j, (j + length PRE + 1 < S a)%nat -> token_at (zbytes tb) PRE (zbytes lb) j = false) ->
    evt rsegs Q
      (MS (mkR x1 sq gp tp x5 x6 x7 lw plw x10 x11 x12 x13 x14 x15 x16 x17 pw tw x20
               (Z_to_bv 64 (bv_unsigned tw + Z.of_nat a)) x22 (Z_to_bv 64 (bv_unsigned plw + 1))
               (Z_to_bv 64 (- bv_unsigned plw)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1) (Z_to_bv 64 58) x28 x29 x30 x31)
          F (Z_to_bv 64 0x142dc) fc None m1 (seg_rom rsegs))).
  { intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 HTb1 HLb1
      GC1 GW1 INV1.
    zstep. nt. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply STRSTR with (hb := skipn (S a) tb) (hs := ts) (nb := lb) (ns := ls) (lo := lo).
      - rewrite unsigned_lit by lia.
        replace (bv_unsigned tw + Z.of_nat a + 1) with (bv_unsigned tw + Z.of_nat (S a)) by lia.
        apply cstr_suffix; [exact HTb1|exact TNZ|exact TSL|lia].
      - split; [exact HLb1|split; [exact LNZ|exact LSL]].
      - exact HLN.
      - rewrite ?unsigned_lit by lia. lia.
      - exact GC1.
      - exists g. exact GW1.
      - unfold STRSTR_K. lia.
      - unfold STRSTR_K. lia.
      - exact MI1.
      - exact ST1.
      - unfold STRSTR_K. lia.
      - unfold off_stack, STRSTR_K. rewrite unsigned_lit by lia. rewrite length_skipn. lia.
      - unfold STRSTR_K. exact DL. }
    unfold STRSTR_K. post_call rsegs m1.
    match goal with M : munch _ m ?mm |- _ => rename mm into m2 end.
    rewrite zbytes_skipn in POST.
    destruct (find_sub (skipn (S a) (zbytes tb)) (zbytes lb)) as [i|] eqn:FS; subst.
    + apply find_sub_some in FS as [FS1 FS2]. rewrite mt_skipn in FS1 by (rewrite length_zbytes; lia).
      pose proof (mt_len _ _ _ FS1) as FL. rewrite !length_zbytes in FL.
      zstep. zstep. rewrite eqb_small by lia. if_false. zstep.
      replace (bv_unsigned tw + Z.of_nat a + 1 + Z.of_nat i) with (bv_unsigned tw + Z.of_nat (S a + i)) by lia.
      eapply IH with (a := (S a + i)%nat);
        [lia|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption|exact FS1| |].
      * apply inv_skip with (b := S a); [exact INV1|]. intros k Hk.
        replace k with (S a + (k - S a))%nat by lia. rewrite <- mt_skipn by (rewrite length_zbytes; lia).
        apply FS2. lia.
      * intros m' r y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
          y30 y31 MU' WM' MI' ST' FR' R'.
        eapply CONT; [eapply munch_trans; [exact MU1|exact MU']|eapply wmono_trans; [exact WM1|exact WM']|
                      exact MI'|exact ST'|exact FR'|exact R'].
    + zstep. zstep. if_true.
      eapply CONT; [exact MU1|exact WM1|eassumption|eassumption|eassumption|].
      replace (token (zbytes tb) PRE (zbytes lb)) with false; [reflexivity|].
      symmetry. apply (token_false _ _ _ (S a)); [|exact INV1].
      intros k Hk. replace k with (S a + (k - S a))%nat by lia. rewrite <- mt_skipn by (rewrite length_zbytes; lia).
      apply find_sub_none. exact FS. }
  zstep. zstep.
  rewrite lts_small by lia.
  destruct (Z.ltb_spec (bv_unsigned tw + Z.of_nat a - bv_unsigned tw) (bv_unsigned plw + 1)) as [HP|HP].
  - eapply CONTINUE; [apply munch_refl|apply wmono_refl|exact MI|exact ST|exact FRM|exact HTb|exact HLb|exact GC|
                      exact GW|].
    apply inv_step; [exact INV|]. intros Hl. exfalso. lia.
  - assert (TAM : token_at (zbytes tb) PRE (zbytes lb) (a - Z.to_nat (bv_unsigned plw) - 1) =
      zl_eqb (firstn (Z.to_nat (bv_unsigned plw)) (skipn (a - Z.to_nat (bv_unsigned plw) - 1) (zbytes tb))) PRE
      && (byte_at (zbytes tb) (a - 1) =? 58)
      && match (a - Z.to_nat (bv_unsigned plw) - 1)%nat with
         | O => true
         | S j' => negb (name_char (byte_at (zbytes tb) j')) && negb (byte_at (zbytes tb) j' =? 46)
         end
      && negb (name_char (byte_at (zbytes tb) (a + length lb)))).
    { rewrite token_at_match.
      - rewrite LPRE, length_zbytes.
        replace (a - Z.to_nat (bv_unsigned plw) - 1 + Z.to_nat (bv_unsigned plw))%nat with (a - 1)%nat by lia.
        replace (a - 1 + 1 + length lb)%nat with (a + length lb)%nat by lia.
        reflexivity.
      - rewrite LPRE. replace (a - Z.to_nat (bv_unsigned plw) - 1 + Z.to_nat (bv_unsigned plw) + 1)%nat with a by lia.
        exact MT. }
    assert (END : forall (m3 : word -> option byte)
              (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 : word),
      munch [(bv_unsigned sq - 2256, bv_unsigned sq)] m m3 -> wmono rsegs m m3 ->
      mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sq) -> rw_cells rsegs m3 (bv_unsigned sq) FRC ->
      bytes_at rsegs m3 (bv_unsigned tw) (tb ++ Z_to_bv 8 0 :: ts) ->
      bytes_at rsegs m3 (bv_unsigned lw) (lb ++ Z_to_bv 8 0 :: ls) ->
      bytes_at rsegs m3 0x1e368 (le8 (Z_to_bv 64 0x4f978)) -> bytes_at rsegs m3 0x4f978 (le8 g) ->
      token_at (zbytes tb) PRE (zbytes lb) (a - Z.to_nat (bv_unsigned plw) - 1)
        = negb (name_char (byte_at (zbytes tb) (a + length lb))) ->
      evt rsegs Q
        (MS (mkR x1 sq gp tp x5 x6 x7 lw plw x10 x11 x12 x13 x14 x15 x16 x17 pw tw x20
                 (Z_to_bv 64 (bv_unsigned tw + Z.of_nat a)) x22 (Z_to_bv 64 (bv_unsigned plw + 1))
                 (Z_to_bv 64 (- bv_unsigned plw)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1) (Z_to_bv 64 58) x28 x29 x30 x31)
            F (Z_to_bv 64 0x14338) fc None m3 (seg_rom rsegs))).
    { intros m3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 MU3 WM3 MI3 ST3 FR3 HTb3 HLb3
        GC3 GW3 TE.
      zstep. zstep. zstep. nt. zstep. zstep.
      pose proof (rd_text m3 (bv_unsigned tw) tb ts (a + length lb) HTb3 ltac:(lia)) as RD3.
      zstep. cbv beta.
      rewrite (byte_at_zbytes tb ts (a + length lb)) by lia.
      pose proof (byte_at_range tb (a + length lb)) as BR3.
      remember (byte_at (zbytes tb) (a + length lb)) as c eqn:Ec.
      zstep. zstep.
      eapply evt_cut.
      { eapply ISALNUM; [rewrite unsigned_lit by lia; lia|exact MI3|exact ST3]. }
      post_call rsegs m3.
      rewrite unsigned_lit in POST by lia.
      zstep.
      destruct (is_alnum c) eqn:AL.
      { pose proof (isal_true _ _ POST ltac:(first [exact AL|reflexivity])) as X1.
        if_true.
        eapply CONTINUE; [exact MU3|exact WM3|eassumption ..|].
        apply inv_step; [exact INV|]. intros _. rewrite LPRE, TE. unfold name_char. rewrite AL. reflexivity. }
      pose proof (isal_false _ _ POST ltac:(first [exact AL|reflexivity])) as X1.
      if_false.
      pose proof (nc_parts c BR3 AL) as NC.
      zstep. zstep.
      rewrite (bv_ltu_Z (Z_to_bv 64 58)), !unsigned_lit_wrap.
      destruct (Z.ltb_spec (58 mod 2^64) ((c + -37) mod 2^64)) as [HB|HB].
      2:{ zstep. zstep. zstep. zstep.
          rewrite eqb_small by (first [lia | pose proof (land1_range (324259173172773121 ≫ ((c + -37) mod 64))); lia]).
          destruct (Z.eqb_spec (Z.land (324259173172773121 ≫ ((c + -37) mod 64)) 1) 0) as [HM|HM]; [if_false|if_true].
          2:{ eapply CONTINUE; [exact MU3|exact WM3|eassumption ..|].
              apply inv_step; [exact INV|]. intros _. rewrite LPRE, TE, NC.
              try rewrite (proj2 (Z.ltb_ge _ _) HB). try rewrite (proj2 (Z.eqb_neq _ _) HM). reflexivity. }
          zstep. zstep. zstep.
          rewrite sx_sign by lia.
          destruct (Z.leb_spec 128 c) as [HS|HS].
          - eapply CONTINUE; [exact MU3|exact WM3|eassumption ..|].
            apply inv_step; [exact INV|]. intros _. rewrite LPRE, TE, NC.
            try rewrite (proj2 (Z.leb_le _ _) HS). rewrite orb_true_r. reflexivity.
          - zstep.
            eapply CONT; [exact MU3|exact WM3|eassumption|eassumption|eassumption|].
            rewrite (token_true _ _ _ (a - Z.to_nat (bv_unsigned plw) - 1)); [reflexivity|].
            rewrite TE, NC. try rewrite (proj2 (Z.ltb_ge _ _) HB). try rewrite (proj2 (Z.eqb_eq _ _) HM).
            try rewrite (proj2 (Z.leb_gt _ _) HS). reflexivity. }
      zstep. zstep. zstep.
      rewrite sx_sign by lia.
      destruct (Z.leb_spec 128 c) as [HS|HS].
      - eapply CONTINUE; [exact MU3|exact WM3|eassumption ..|].
        apply inv_step; [exact INV|]. intros _. rewrite LPRE, TE, NC.
        try rewrite (proj2 (Z.leb_le _ _) HS). rewrite orb_true_r. reflexivity.
      - zstep.
        eapply CONT; [exact MU3|exact WM3|eassumption|eassumption|eassumption|].
        rewrite (token_true _ _ _ (a - Z.to_nat (bv_unsigned plw) - 1)); [reflexivity|].
        rewrite TE, NC. try rewrite (proj2 (Z.ltb_lt _ _) HB). try rewrite (proj2 (Z.leb_gt _ _) HS).
        reflexivity. }
    pose proof (munch_refl [(bv_unsigned sq - 2256, bv_unsigned sq)] m) as MU0.
    pose proof (wmono_refl rsegs m) as WM0.
    zstep. nt. zstep. zstep. nt. zstep. zstep. nt. zstep. zstep.
    pose proof (rd_text m (bv_unsigned tw) tb ts (a - 1) HTb ltac:(lia)) as RD1.
    zstep. cbv beta.
    rewrite (byte_at_zbytes tb ts (a - 1)) by lia.
    pose proof (byte_at_range tb (a - 1)) as BR1.
    zstep.
    rewrite eqb_small by lia.
    destruct (Z.eqb_spec (byte_at (zbytes tb) (a - 1)) 58) as [HC|HC]; [if_false|if_true].
    2:{ eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
        apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM.
        try rewrite (proj2 (Z.eqb_neq _ _) HC). rewrite ?andb_false_r. reflexivity. }
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply STRNCMP with (lb := skipn (a - Z.to_nat (bv_unsigned plw) - 1) tb) (rb := skipn (Z.to_nat q) tb) (lo := lo).
      - rewrite unsigned_lit by lia.
        replace (bv_unsigned tw + Z.of_nat a + - bv_unsigned plw + -1)
          with (bv_unsigned tw + Z.of_nat (a - Z.to_nat (bv_unsigned plw) - 1)) by lia.
        apply cstr0_suffix with (ts := ts); [exact HTb|exact TNZ|lia].
      - rewrite HPRE. replace (bv_unsigned tw + q) with (bv_unsigned tw + Z.of_nat (Z.to_nat q)) by lia.
        apply cstr0_suffix with (ts := ts); [exact HTb|exact TNZ|lia].
      - exact MI.
      - exact ST. }
    post_call rsegs m.
    match goal with M : munch _ m ?mm |- _ => rename mm into m2 end.
    rewrite !zbytes_skipn, !firstn_app_long in POST by (rewrite length_skipn, length_zbytes; lia).
    rewrite <- zl_eqb_eq in POST.
    zstep.
    destruct (zl_eqb (firstn (Z.to_nat (bv_unsigned plw)) (skipn (a - Z.to_nat (bv_unsigned plw) - 1) (zbytes tb)))
                PRE) eqn:ZE.
    2:{ assert (X0 : forall r : word, (bv_unsigned r = 0 <-> false = true) -> bv_unsigned r <> 0)
          by (intros r H E; apply H in E; discriminate).
        apply X0 in POST. if_false.
        eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
        apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM. try rewrite ZE. reflexivity. }
    assert (X0 : forall r : word, (bv_unsigned r = 0 <-> true = true) -> bv_unsigned r = 0)
      by (intros r H; apply H; reflexivity).
    apply X0 in POST. if_true.
    zstep.
    rewrite (bv_ltu_Z tw), (unsigned_lit (bv_unsigned tw + Z.of_nat a + - bv_unsigned plw + -1)) by lia.
    destruct (Nat.eq_dec (a - Z.to_nat (bv_unsigned plw) - 1) 0) as [J0|J0].
    { if_true.
      eapply END; [exact MU0|exact WM0|eassumption ..|].
      rewrite TAM. try rewrite ZE. rewrite J0. reflexivity. }
    if_false.
    assert (TAM2 : token_at (zbytes tb) PRE (zbytes lb) (a - Z.to_nat (bv_unsigned plw) - 1) =
      negb (name_char (byte_at (zbytes tb) (a - Z.to_nat (bv_unsigned plw) - 2)))
      && negb (byte_at (zbytes tb) (a - Z.to_nat (bv_unsigned plw) - 2) =? 46)
      && negb (name_char (byte_at (zbytes tb) (a + length lb)))).
    { rewrite TAM. try rewrite ZE. destruct (a - Z.to_nat (bv_unsigned plw) - 1)%nat as [|j'] eqn:EJ; [lia|].
      replace (a - Z.to_nat (bv_unsigned plw) - 2)%nat with j' by lia. reflexivity. }
    zstep. nt.
    pose proof (rd_text m2 (bv_unsigned tw) tb ts (a - Z.to_nat (bv_unsigned plw) - 2) HTb ltac:(lia)) as RD2.
    zstep. cbv beta.
    rewrite (byte_at_zbytes tb ts (a - Z.to_nat (bv_unsigned plw) - 2)) by lia.
    pose proof (byte_at_range tb (a - Z.to_nat (bv_unsigned plw) - 2)) as BR2.
    remember (byte_at (zbytes tb) (a - Z.to_nat (bv_unsigned plw) - 2)) as c2 eqn:Ec2.
    zstep. zstep. clear POST.
    eapply evt_cut.
    { eapply ISALNUM; [rewrite unsigned_lit by lia; lia|eassumption|eassumption]. }
    post_call rsegs m2.
    rewrite unsigned_lit in POST by lia.
    zstep.
    destruct (is_alnum c2) eqn:AL2.
    { pose proof (isal_true _ _ POST ltac:(first [exact AL2|reflexivity])) as X2.
      if_true.
      eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
      apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM2. unfold name_char. rewrite AL2. reflexivity. }
    pose proof (isal_false _ _ POST ltac:(first [exact AL2|reflexivity])) as X2.
    if_false.
    pose proof (nc_parts c2 BR2 AL2) as NC2.
    zstep. zstep.
    rewrite (bv_ltu_Z (Z_to_bv 64 58)), !unsigned_lit_wrap.
    destruct (Z.ltb_spec (58 mod 2^64) ((c2 + -37) mod 2^64)) as [HB2|HB2].
    2:{ zstep. zstep. zstep. zstep.
        rewrite eqb_small by (first [lia | pose proof (land1_range (324259173172773121 ≫ ((c2 + -37) mod 64))); lia]).
        destruct (Z.eqb_spec (Z.land (324259173172773121 ≫ ((c2 + -37) mod 64)) 1) 0) as [HM2|HM2];
          [if_false|if_true].
        2:{ eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
            apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM2, NC2.
            try rewrite (proj2 (Z.ltb_ge _ _) HB2). try rewrite (proj2 (Z.eqb_neq _ _) HM2). reflexivity. }
        zstep. zstep.
        rewrite sl_sign by lia.
        destruct (Z.leb_spec 128 c2) as [HS2|HS2]; try first [if_true|if_false].
        - eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
          apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM2, NC2.
          try rewrite (proj2 (Z.leb_le _ _) HS2). rewrite orb_true_r. reflexivity.
        - zstep. zstep.
          rewrite eqb_small by lia.
          destruct (Z.eqb_spec c2 46) as [HD|HD]; try first [if_true|if_false].
          + eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
            apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM2.
            try rewrite (proj2 (Z.eqb_eq _ _) HD). cbn [negb]. rewrite ?andb_false_r. reflexivity.
          + eapply END; [exact MU0|exact WM0|eassumption ..|].
            rewrite TAM2, NC2. try rewrite (proj2 (Z.ltb_ge _ _) HB2). try rewrite (proj2 (Z.eqb_eq _ _) HM2).
            try rewrite (proj2 (Z.leb_gt _ _) HS2). try rewrite (proj2 (Z.eqb_neq _ _) HD). reflexivity. }
    zstep. zstep.
    rewrite sl_sign by lia.
    destruct (Z.leb_spec 128 c2) as [HS2|HS2]; try first [if_true|if_false].
    * eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
      apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM2, NC2.
      try rewrite (proj2 (Z.leb_le _ _) HS2). rewrite orb_true_r. reflexivity.
    * zstep. zstep.
      rewrite eqb_small by lia.
      destruct (Z.eqb_spec c2 46) as [HD|HD]; try first [if_true|if_false].
      + eapply CONTINUE; [exact MU0|exact WM0|eassumption ..|].
        apply inv_step; [exact INV|]. intros _. rewrite LPRE, TAM2.
        try rewrite (proj2 (Z.eqb_eq _ _) HD). cbn [negb]. rewrite ?andb_false_r. reflexivity.
      + eapply END; [exact MU0|exact WM0|eassumption ..|].
        rewrite TAM2, NC2. try rewrite (proj2 (Z.ltb_lt _ _) HB2).
        try rewrite (proj2 (Z.leb_gt _ _) HS2). try rewrite (proj2 (Z.eqb_neq _ _) HD). reflexivity.
Qed.

End HpLoop.

Lemma hp_epilogue : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m0 m : word -> option byte) (junk : list byte) (R : word -> Prop)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31 : word),
  munch [(bv_unsigned sp - 2384, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp + -128 ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  R x10 ->
  evt rsegs (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 2384 m0 [] R)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14384) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 m junk R x1 x5 x6 x7 x8 x9 x10 x11 x12 x13
    x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 MU WM MI ST LO FR HR.
  pose proof (rw_cells_bound rsegs m _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  do 14 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. finish.
Qed.

Theorem has_prefixed_holds : strlen_contract -> strstr_contract -> strncmp_contract -> isalnum_contract ->
  has_prefixed_contract.
Proof.
  intros STRLEN STRSTR STRNCMP ISALNUM. unfold has_prefixed_contract, HAS_PREFIXED, HAS_PREFIXED_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo q
    tb ts lb ls HT HL HLN GC GW GB1 GB2 HTX HTN HQ HQP HPRE HMI ST LO DT DL.
  destruct HT as (HTb & TNZ & TSL). destruct HL as (HLb & LNZ & LSL). destruct GW as [g GW].
  pose proof (bytes_at_bound _ _ _ _ HTb) as BT. pose proof (bytes_at_bound _ _ _ _ HLb) as BL.
  rewrite length_app in BT, BL. cbn [length] in BT, BL.
  assert (LBP : (1 <= length lb)%nat) by (destruct lb; [contradiction|cbn; lia]).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Rsp, Ra0, Ra2.
  pose proof DT as DT'. pose proof DL as DL'. unfold off_stack in DT', DL'.
  assert (LO0 : 0 <= lo) by (destruct ST as (H0 & _); exact H0).
  pose proof (munch_refl [(bv_unsigned sp - 2384, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 128%nat ST.
  do 20 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  remember (Z_to_bv 64 (bv_unsigned sp + -128)) as sq eqn:Esq.
  assert (Hsq : bv_unsigned sq = bv_unsigned sp + -128) by (rewrite Esq; apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply STRLEN with (bs := lb) (slack := ls) (lo := lo);
      [split; [exact HLb|split; assumption]|eassumption|rewrite Hsq; exact ST]. }
  post_call rsegs m1.
  match type of POST with ?v = _ => subst v end.
  rewrite <- Hsq in FR.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  eapply evt_cut.
  { eapply STRSTR with (hb := tb) (hs := ts) (nb := lb) (ns := ls) (lo := lo).
    - split; [exact HTb|split; assumption].
    - split; [exact HLb|split; assumption].
    - exact HLN.
    - lia.
    - eassumption.
    - exists g. eassumption.
    - unfold STRSTR_K. lia.
    - unfold STRSTR_K. lia.
    - eassumption.
    - rewrite Hsq. eassumption.
    - unfold STRSTR_K. lia.
    - unfold off_stack, STRSTR_K. lia.
    - unfold off_stack, STRSTR_K. lia. }
  unfold STRSTR_K. post_call rsegs m2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  destruct (find_sub (zbytes tb) (zbytes lb)) as [i|] eqn:FS; match type of POST with ?v = _ => subst v end.
  - apply find_sub_some in FS as [FS1 FS2].
    pose proof (mt_len _ _ _ FS1) as FL. rewrite !length_zbytes in FL.
    zstep. rewrite eqb_small by lia. if_false.
    do 12 zstep.
    replace (Z_to_bv 64 (0 - bv_unsigned a2)) with (Z_to_bv 64 (- bv_unsigned a2)) by (f_equal; lia).
    eapply hp_loop with (n := S (length tb)) (a := i) (q := q) (tb := tb) (ts := ts) (lb := lb) (ls := ls) (lo := lo)
      (g := g).
    all: lazymatch goal with
         | |- forall _ : nat, _ =>
             intros j Hj; apply not_true_iff_false; intro E; apply token_at_mt in E;
             rewrite FS2 in E by lia; discriminate
         | |- forall (_ : word -> option byte) (_ : Z), _ =>
             intros m' r y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
               y29 y30 y31 MU' WM' MI' ST' FR' R';
             assert (MUf : munch [(bv_unsigned sp - 2384, bv_unsigned sp)] m m')
               by (eapply munch_trans; [exact MU|eapply munch_weaken; [|exact MU']];
                   unfold sub_fp; cbn [outside]; intros z [Hz _]; split; [lia|exact I]);
             pose proof (wmono_trans rsegs _ _ _ WM WM') as WMf;
             lazymatch type of FR' with
             | rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?c3 :: ?post) =>
                 pose proof (frame_merge mm A [c1; c2; c3] post FR') as FR2
             end;
             cbn [cells_size csize Nat.add] in FR2;
             rewrite Hsq in ST', FR2; subst sq; subst r;
             eapply hp_epilogue; [exact MUf|exact WMf|exact MI'|exact ST'|lia|exact FR2|reflexivity]
         | |- mt _ _ _ = true => exact FS1
         | |- off_stack _ _ _ _ => unfold off_stack; lia
         | |- rw_cells _ _ _ _ => exact FR
         | |- _ => first [assumption | lia]
         end.
  - zstep. if_true.
    lazymatch type of FR with
    | rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?post) => pose proof (frame_merge mm A [c1; c2] post FR) as FR2
    end.
    cbn [cells_size csize Nat.add] in FR2.
    match goal with H : stk _ _ _ (bv_unsigned sq) |- _ => rewrite Hsq in H end.
    rewrite Hsq in FR2. subst sq.
    eapply hp_epilogue; [eassumption|eassumption|eassumption|eassumption|lia|exact FR2|].
    replace (token (zbytes tb) (firstn (Z.to_nat (bv_unsigned a2)) (skipn (Z.to_nat q) (zbytes tb))) (zbytes lb))
      with false; [reflexivity|].
    symmetry. apply (token_false _ _ _ 0); [intros k _; apply find_sub_none; exact FS|intros j Hj; lia].
Qed.
