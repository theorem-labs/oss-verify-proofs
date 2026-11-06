(* G4.ExEntry: expected 0x81130 from its entry to EX_L / EX_R (ex_seg_entry, FMW_ex_base.v:163), the kit.
   The segment is cut once more inside: EX_WL (ex_whole's loop head, s4 = a '<' of text), EX_B (0x811c4, a0 = r + 1 + n
   after strncmp (r + 1, uri, n) = 0, the instrumented load of r[1 + n] next), EX_S (0x811dc, strchr (r + 1, '<') next)
   and EX_MS (the scan's setup). Each cut carries ex_com and the registers it names; each piece builds its own symbolic
   state from them (FMW_plain.v's L_entry pattern) and the shadow base is s9 (EE_Bx, atom 25, as G3's LP_Bx). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the cuts inside the segment ---- *)
Definition EX_B : Z := 0x811c4.   (* a0 = r + 1 + n; the instrumented load of r[1 + n] next, fuzz_manifest.c:119 *)
Definition EX_S : Z := 0x811dc.   (* strchr (r + 1, '<') next, :118 *)
Definition EE_Bx : sv := SOff 25 0.   (* s9, the shadow base *)
Definition EE_SB : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition EE_SP : afact := mkAF (2 ^ 46) (2 ^ 47) 4.

(* ---- the model facts the walk reads off the runtime answers ---- *)
Lemma ee_nth_app0 : forall (l : list Z) i, nth i (l ++ [0]) 0 = nth i l 0.
Proof.
  intros l i. destruct (Nat.lt_ge_cases i (length l)) as [H|H].
  - rewrite app_nth1 by exact H. reflexivity.
  - rewrite app_nth2 by exact H. rewrite (nth_overflow l) by exact H.
    destruct (i - length l)%nat as [|k]; [reflexivity|]. cbn. destruct k; reflexivity.
Qed.
(* (G3 FMW_rd_pre_k.v rdp_nth_skipn) *)
Lemma ee_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity; [destruct j; reflexivity | apply IH].
Qed.
Lemma ee_first_before : forall l c j, first_at l c j -> forall k, (k < j)%nat -> nth k l 0 <> c.
Proof.
  intros l c j (Hj & _ & Hn) k Hk E.
  assert (L : length (firstn j l) = j) by (rewrite length_firstn; lia).
  rewrite <- (firstn_skipn j l) in E. rewrite app_nth1 in E by lia.
  apply Hn. rewrite <- E. apply nth_In. lia.
Qed.
Lemma ee_not_in : forall l c, ~ In c l -> forall k, (k < length l)%nat -> nth k l 0 <> c.
Proof. intros l c H k Hk E. apply H. rewrite <- E. apply nth_In. exact Hk. Qed.

Lemma ee_names_0 : forall tb ub, length ub = 0%nat -> ManifestModel.names tb ub = 0.
Proof. intros tb ub H. unfold ManifestModel.names. rewrite H. reflexivity. Qed.
Lemma ee_names_scan : forall tb ub, (length ub <> 0)%nat -> ManifestModel.whole tb ub = false ->
  ManifestModel.names tb ub = ManifestModel.scan tb ub 0 0 (S (length tb)).
Proof.
  intros tb ub H Hw. unfold ManifestModel.names. destruct (length ub =? 0)%nat eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - rewrite Hw. reflexivity.
Qed.
Lemma ee_names_1 : forall tb ub j, (length ub <> 0)%nat -> (j <= length tb)%nat ->
  nth j tb 0 = 60 -> firstn (length ub) (skipn (S j) tb) = ub -> nth (S j + length ub) tb 0 = 62 ->
  ManifestModel.names tb ub = 1.
Proof.
  intros tb ub j H Hj H60 Hf H62. unfold ManifestModel.names. destruct (length ub =? 0)%nat eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - rewrite (expected_m.whole_true_of tb ub j Hj); [reflexivity|].
    apply expected_m.whole_at_spec. unfold ManifestModel.byte_at. tauto.
Qed.
Lemma ee_whole_at_firstn : forall tb ub j, firstn (length ub) (skipn (S j) tb) <> ub ->
  ManifestModel.whole_at tb ub j = false.
Proof.
  intros tb ub j H. destruct (ManifestModel.whole_at tb ub j) eqn:E; [|reflexivity].
  apply expected_m.whole_at_spec in E. tauto.
Qed.
Lemma ee_whole_at_close : forall tb ub j, nth (S j + length ub) tb 0 <> 62 ->
  ManifestModel.whole_at tb ub j = false.
Proof.
  intros tb ub j H. destruct (ManifestModel.whole_at tb ub j) eqn:E; [|reflexivity].
  apply expected_m.whole_at_spec in E. unfold ManifestModel.byte_at in E. tauto.
Qed.
Lemma ee_before_ext : forall tb ub j j2, (j <= j2)%nat ->
  (forall k, (k < j)%nat -> ManifestModel.whole_at tb ub k = false) ->
  (forall k, (j <= k < j2)%nat -> nth k tb 0 <> 60) ->
  forall k, (k < j2)%nat -> ManifestModel.whole_at tb ub k = false.
Proof.
  intros tb ub j j2 Hj H1 H2 k Hk. destruct (Nat.lt_ge_cases k j) as [Hl|Hl]; [exact (H1 k Hl)|].
  apply expected_m.whole_at_not_lt. unfold ManifestModel.byte_at. apply H2. lia.
Qed.
Lemma ee_whole_false : forall tb ub j,
  (forall k, (k < j)%nat -> ManifestModel.whole_at tb ub k = false) ->
  (forall k, (j <= k < length tb)%nat -> nth k tb 0 <> 60) -> ManifestModel.whole tb ub = false.
Proof.
  intros tb ub j H1 H2. apply expected_m.whole_false_of. intros k Hk.
  destruct (Nat.lt_ge_cases k j) as [Hl|Hl]; [exact (H1 k Hl)|].
  apply expected_m.whole_at_not_lt. unfold ManifestModel.byte_at.
  destruct (Nat.lt_ge_cases k (length tb)) as [Ht|Ht]; [apply H2; lia|].
  rewrite nth_overflow by exact Ht. discriminate.
Qed.
Lemma ee_strn_true : forall n l ub, length ub = n -> Forall (fun c => c <> 0) ub -> strn_eq n l ub ->
  (n <= length l)%nat /\ firstn n l = ub.
Proof.
  intros n l ub Hn Hnz H. unfold strn_eq in H.
  assert (Hu : firstn n (ub ++ [0]) = ub).
  { rewrite firstn_app, <- Hn, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. }
  rewrite Hu in H. rewrite firstn_app in H.
  destruct (Nat.le_gt_cases n (length l)) as [Hle|Hgt].
  - replace (n - length l)%nat with 0%nat in H by lia. cbn in H. rewrite app_nil_r in H.
    split; [exact Hle | exact H].
  - exfalso. rewrite firstn_all2 in H by lia. destruct (n - length l)%nat as [|k] eqn:E; [lia|]. cbn in H.
    rewrite Forall_forall in Hnz. apply (Hnz 0); [|reflexivity].
    rewrite <- H. apply in_or_app. right. left. reflexivity.
Qed.
Lemma ee_strn_false : forall n l ub, length ub = n -> ~ strn_eq n l ub -> firstn n l <> ub.
Proof.
  intros n l ub Hn H E. apply H. unfold strn_eq.
  assert (Hle : (n <= length l)%nat).
  { pose proof (f_equal (@length Z) E) as L. rewrite length_firstn in L. lia. }
  rewrite !firstn_app. replace (n - length l)%nat with 0%nat by lia. replace (n - length ub)%nat with 0%nat by lia.
  cbn. rewrite !app_nil_r, E, <- Hn, firstn_all. reflexivity.
Qed.

(* ---- a suffix of a C string (G5 FMW_kitS.v cstr_ok_suffix, shadow_hull_vis_sub; copied) ---- *)
Lemma ee_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
  intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
  assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
    by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
  assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
    by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
  lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma ee_cstr_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
  intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
  assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
  assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
  split; [split|].
  - rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (garr8_app tfibsegs) in Hg as [_ Hg].
    rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
  - rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
    split; [intros x Hx; apply Hra; lia|].
    split; [apply (ee_hull_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
    intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.
(* the byte at p + i of a C string (i <= length, the NUL included) *)
Lemma ee_cstr_byte : forall (W : world tfibsegs) mem p l i, (i <= length l)%nat ->
  cstr_ok tfibsegs W mem p l ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i) 1 (nth i l 0) /\ 0 <= nth i l 0 < 256.
Proof.
  intros W mem p l i Hi ((HGa & _) & _).
  destruct (HGa i ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  rewrite ee_nth_app0 in Vc, Rc. split; [exact Vc|]. cbn in Rc. lia.
Qed.
End s.

(* ---- memory kept outside a window ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition ee_kept (W : world tfibsegs) (lo hi : Z) (m0 m1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m0 a.

Lemma ee_kept_refl : forall W lo hi m, ee_kept W lo hi m m.
Proof. intros W lo hi m a _ _. reflexivity. Qed.
Lemma ee_kept_trans : forall W lo hi l1 h1 l2 h2 m0 m1 m2,
  ee_kept W l1 h1 m0 m1 -> ee_kept W l2 h2 m1 m2 -> lo <= l1 -> h1 <= hi -> lo <= l2 -> h2 <= hi ->
  ee_kept W lo hi m0 m2.
Proof.
  intros W lo hi l1 h1 l2 h2 m0 m1 m2 K1 K2 H1 H2 H3 H4 a Ha Hn.
  rewrite (K2 a Ha) by lia. apply K1; [exact Ha | lia].
Qed.
Lemma ee_kept_nowin : forall E rs W lo hi (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ee_kept W lo hi m m'.
Proof. intros E rs W lo hi m m' HF Hw a Ha _. exact (fw_nowin tfibsegs E rs (w_H W) m m' HF Hw a Ha). Qed.
Lemma ee_val_kept : forall W lo hi m m' a n v, ee_kept W lo hi m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= lo \/ hi <= a) -> val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W m') a n v.
Proof.
  intros W lo hi m m' a n v K Ha Hn Hd Hv k Hk.
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m'); [apply Hv; exact Hk|].
  apply K; lia.
Qed.
Lemma ee_low : forall W lo hi m m', ee_kept W lo hi m m' -> alloc_ceiling <= lo -> fw_low tfibsegs (w_H W) m m'.
Proof. intros W lo hi m m' K Hl a Ha. pose proof asan_consts as (C1 & _). apply K; lia. Qed.

(* ---- the base facts of expected's entry ---- *)
Lemma ee_base_facts : forall cx, ex_base B cx ->
  cx_sp cx mod 16 = 0 /\ alloc_ceiling + STK_expected <= cx_sp cx /\ cx_sp cx <= 2 ^ 47 /\
  getr (cx_regs cx) 3 = w64 (as_gp B) /\ getr (cx_regs cx) 4 = w64 (as_tp B).
Proof.
  intros cx HB. destruct HB as ((HPRE & _) & _).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold cx_sp. split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [exact Hgp | exact Htp].
Qed.

(* ex_com carried across a step that keeps sp, gp, tp, s9 and changes memory only between the stack's floor and the
   saved registers (F + 104) *)
Lemma ee_com_keep : forall cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  ee_kept W3 (cx_sp cx - STK_expected) (cx_F cx + 104) mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  ex_com B cx ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4 K Q2 Q3 Q4 Q25.
  pose proof (ee_base_facts cx HB) as (Hal & Hsp & Hsp47 & _ & _).
  pose proof asan_consts as (C1 & _).
  assert (HSTK : STK_expected = 8432) by reflexivity.
  destruct HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  assert (KL : fw_low tfibsegs (w_H W3) mem3 mem4) by (apply (ee_low W3 _ _ _ _ K); lia).
  split; [exact HJ4|]. split; [exact Hbl|].
  split; [exact (fw_glob_low tfibsegs W3 mem3 mem4 _ _ _ _ KL HGL)|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q25; exact R25|].
  split.
  { unfold ex_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hs.
    apply (ee_val_kept W3 _ _ mem3 mem4 _ _ _ K); [| | | exact (HSV s Hs)];
      cbv [EX_SAVED In] in Hs; unfold cx_F in *;
      repeat (destruct Hs as [<-|Hs]; [cbn [fst]; lia|]); destruct Hs. }
  split; [exact (fw_rodata_low tfibsegs B _ mem3 mem4 fmw_segs_low KL HRO)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Ct)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Cu)|].
  split; [exact Kt | exact Ku].
Qed.

(* ex_com at a state reached from expected's entry with no block or world change *)
Lemma ee_com_entry : forall cx regs4 mem4 md4,
  ex_base B cx ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] (cx_ly cx) (cx_S cx) (cx_W cx) mem4 md4 0 ->
  fw_low tfibsegs (w_H (cx_W cx)) (cx_mem cx) mem4 ->
  getr regs4 2 = w64 (cx_F cx) -> getr regs4 3 = getr (cx_regs cx) 3 -> getr regs4 4 = getr (cx_regs cx) 4 ->
  getr regs4 25 = w64 SHADOW_OFF -> ex_saved_ok cx (cx_W cx) mem4 ->
  ex_com B cx (cx_ly cx) (cx_S cx) (cx_W cx) regs4 mem4 md4.
Proof.
  intros cx regs4 mem4 md4 HB HJ4 KL R2 R3 R4 R25 HSV.
  destruct HB as ((HPRE & HRO) & HGL & _ & _ & Ct & Cu & Kt & Ku & _).
  split; [exact HJ4|]. split; [reflexivity|].
  split; [exact (fw_glob_low tfibsegs _ _ mem4 _ _ _ _ KL HGL)|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R25|]. split; [exact HSV|].
  split; [exact (fw_rodata_low tfibsegs B _ _ mem4 fmw_segs_low KL HRO)|].
  split; [exact (fw_cstr_low tfibsegs _ _ mem4 _ _ KL Ct)|].
  split; [exact (fw_cstr_low tfibsegs _ _ mem4 _ _ KL Cu)|].
  split; [exact Kt | exact Ku].
Qed.

(* ---- the cuts' invariants ---- *)
(* every cut: the strings, uri in s1, n in s2, text in s7 *)
Definition ex_cut (cx : ecx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ (length (cx_ub cx) <> 0)%nat /\
  getr regs3 9 = w64 (cx_u cx) /\ getr regs3 18 = w64 (cx_n cx) /\ getr regs3 23 = w64 (cx_t cx).
(* no "<uri>" starts before j *)
Definition ex_before (cx : ecx) (j : nat) : Prop :=
  forall k, (k < j)%nat -> ManifestModel.whole_at (cx_tb cx) (cx_ub cx) k = false.
(* EX_MS: no "<uri>" in text *)
Definition ex_at_MS (cx : ecx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_cut cx ly3 S3 W3 regs3 mem3 md3 /\ ManifestModel.whole (cx_tb cx) (cx_ub cx) = false.
(* EX_WL: s4 = text + j, text[j] = '<', s0 = '>' *)
Definition ex_at_WL (cx : ecx) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_cut cx ly3 S3 W3 regs3 mem3 md3 /\ (j < length (cx_tb cx))%nat /\ nth j (cx_tb cx) 0 = 60 /\ ex_before cx j /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat j) /\ getr regs3 8 = w64 62.
(* EX_B: strncmp (text + j + 1, uri, n) = 0; a0 = text + j + 1 + n, s3 = text + j + 1 *)
Definition ex_at_B (cx : ecx) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_cut cx ly3 S3 W3 regs3 mem3 md3 /\ (S j + length (cx_ub cx) <= length (cx_tb cx))%nat /\
  nth j (cx_tb cx) 0 = 60 /\ firstn (length (cx_ub cx)) (skipn (S j) (cx_tb cx)) = cx_ub cx /\ ex_before cx j /\
  getr regs3 10 = w64 (cx_t cx + Z.of_nat j + 1 + cx_n cx) /\ getr regs3 19 = w64 (cx_t cx + Z.of_nat j + 1) /\
  getr regs3 8 = w64 62.
(* EX_S: no "<uri>" starts at or before j; s3 = text + j + 1 *)
Definition ex_at_S (cx : ecx) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_cut cx ly3 S3 W3 regs3 mem3 md3 /\ (j < length (cx_tb cx))%nat /\ ex_before cx (S j) /\
  getr regs3 19 = w64 (cx_t cx + Z.of_nat j + 1) /\ getr regs3 8 = w64 62.

(* the continuation ex_seg_entry hands over, and the loop's re-entry *)
Definition ex_K (cx : ecx) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, ex_at_L B cx 0 0 (S (length (cx_tb cx))) ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post B cx).
Definition ex_WL_from (cx : ecx) (j0 : nat) : Prop :=
  forall j ly3 S3 W3 regs3 mem3 md3, (j0 < j)%nat -> ex_at_WL cx j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_WL regs3 mem3 md3) (ex_post B cx).

(* ex_cut carried across a step: the four registers ex_com names and s1, s2, s7 *)
Lemma ee_cut_keep : forall cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_cut cx ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  ee_kept W3 (cx_sp cx - STK_expected) (cx_F cx + 104) mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 23 = getr regs3 23 ->
  ex_cut cx ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HB & HC & Hn & R9 & R18 & R23) HJ4 K Q2 Q3 Q4 Q25 Q9 Q18 Q23.
  split; [exact HB|]. split; [exact (ee_com_keep cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4 K Q2 Q3 Q4 Q25)|].
  split; [exact Hn|]. split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18 | rewrite Q23; exact R23].
Qed.

(* ---- the pieces of the segment (one file each; FMW_ex_entry.v composes them) ---- *)
(* the scan's setup 0x81200..0x8125c, then EX_L with i = d = 0 (FMW_ex_entry_ms.v) *)
Definition ex_MS_seg : Prop :=
  forall cx ly3 S3 W3 regs3 mem3 md3, ex_K cx -> ex_at_MS cx ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_MS regs3 mem3 md3) (ex_post B cx).
(* strchr (r + 1, '<') and its branch: EX_WL at the next '<' or EX_MS (FMW_ex_entry_s.v) *)
Definition ex_S_seg : Prop :=
  forall cx j ly3 S3 W3 regs3 mem3 md3, ex_K cx -> ex_WL_from cx j -> ex_at_S cx j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_S regs3 mem3 md3) (ex_post B cx).
(* the instrumented load of r[1 + n] and its test against '>': EX_R (a0 = 1) or EX_S (FMW_ex_entry_b.v) *)
Definition ex_B_seg : Prop :=
  forall cx j ly3 S3 W3 regs3 mem3 md3, ex_K cx -> ex_WL_from cx j -> ex_at_B cx j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_B regs3 mem3 md3) (ex_post B cx).
(* the loop head: strncmp (r + 1, uri, n) and its branch: EX_B or EX_S (FMW_ex_entry_wl.v) *)
Definition ex_WL_seg : Prop :=
  forall cx j ly3 S3 W3 regs3 mem3 md3, ex_K cx -> ex_WL_from cx j -> ex_at_WL cx j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_WL regs3 mem3 md3) (ex_post B cx).
End k.

(* ---- tactics (FMW_plain.v pl_mk, G3 lp_g) ---- *)
Ltac ee_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac ee_g HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      rewrite (st_ok_restrict_reg segs H E ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end end;
  cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
