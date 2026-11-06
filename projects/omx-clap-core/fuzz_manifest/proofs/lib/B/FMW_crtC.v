(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_crtC.v, relocated by b_reloc.py (crt): every image
   numeral re-derived by symbol / section / string content, revcheck report (internal path). *)
(* check_round_trip, the two pre-loop snprintf/reader pairs (fuzz_manifest.c:270-273): the glue every pair of the walk
   uses (the snprintf call at a text-buffer destination, the reader call that follows it) and the segments
   crt_segC1 (CRT_P3 -> snprintf tw -> must_name -> CRT_P5) and crt_segC2 (CRT_P5 -> snprintf tx -> as_ruled -> CRT_P7).
   Image B outlines A's `names; li a1,1; bne a0,a1 -> abort` into must_name 0x81a9c, so the names pairs call it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_must_name.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Ltac cs_tac := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.
(* H : c = its value, computed from this image's definitions (the stack budgets of FMH_Base.v) *)
Local Ltac zval H c := let v := eval vm_compute in c in assert (H : c = v) by reflexivity.

(* ---- pure list facts ---- *)
Lemma fa_app : forall (P : Z -> Prop) l1 l2, Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros P l1 l2 H1 H2. induction H1 as [|x l Hx Hl IH]; cbn [app]; [exact H2 | constructor; assumption]. Qed.
Lemma nz_firstn : forall k (l : list Z), Forall (fun c => c <> 0) l -> Forall (fun c => c <> 0) (firstn k l).
Proof.
induction k as [|k IH]; intros l H; [cbn [firstn]; constructor|].
destruct l as [|c l]; cbn [firstn]; [constructor|].
inversion H as [|c0 l0 Hc Hl]; subst. constructor; [exact Hc | exact (IH l Hl)].
Qed.
Lemma nz_skipn : forall k (l : list Z), Forall (fun c => c <> 0) l -> Forall (fun c => c <> 0) (skipn k l).
Proof.
induction k as [|k IH]; intros l H; [cbn [skipn]; exact H|].
destruct l as [|c l]; cbn [skipn]; [constructor|].
inversion H as [|c0 l0 Hc Hl]; subst. exact (IH l Hl).
Qed.
Local Ltac nzlist := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Lemma zdisj_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.
Lemma pairwise_perm_zdisj : forall (l l' : list (Z * Z)), Permutation l l' ->
  pairwise zdisjoint l -> pairwise zdisjoint l'.
Proof.
intros l l' H. induction H as [| x l1 l2 H IH | x y l | l1 l2 l3 H1 IH1 H2 IH2]; intros P; cbn [pairwise] in *.
- exact P.
- destruct P as [HF P]. split; [|exact (IH P)].
  apply Forall_forall. intros z Hz.
  exact (proj1 (Forall_forall _ _) HF z (Permutation_in z (Permutation_sym H) Hz)).
- destruct P as [HFy [HFx Pl]].
  inversion HFy as [|a0 l0 Hyx HFyl]; subst.
  split; [constructor; [exact (zdisj_sym y x Hyx) | exact HFx] | split; [exact HFyl | exact Pl]].
- exact (IH2 (IH1 P)).
Qed.

(* ---- pure facts: the reader calls a used split point makes, and the '>'-free prefix ---- *)
Lemma crt_rest_pos : forall cx k, 0 <= crt_rest cx k.
Proof. intros cx k. unfold crt_rest. lia. Qed.
(* one split point that is used (plain (uri + k) holds): its four calls and the rest from k + 1 *)
Lemma crt_rest_stepP : forall cx k,
  (k < length (cx_ub cx))%nat -> ManifestModel.byte_at (cx_ub cx) (k - 1) <> 62 ->
  ManifestModel.plain_name (skipn k (cx_ub cx)) = true ->
  crt_rest cx k = 4 + crt_rest cx (S k).
Proof.
intros cx k Hk Hb Hp. unfold crt_rest.
replace (length (cx_ub cx) - k + 1)%nat with (S (length (cx_ub cx) - S k + 1)) by lia.
cbn [rt_used].
destruct ((k <? length (cx_ub cx))%nat && negb (ManifestModel.byte_at (cx_ub cx) (k - 1) =? 62))%bool eqn:E.
2:{ exfalso. apply andb_false_iff in E as [E|E];
    [apply Nat.ltb_ge in E; lia | apply Bool.negb_false_iff, Z.eqb_eq in E; exact (Hb E)]. }
destruct (ManifestModel.plain_name (skipn k (cx_ub cx))) eqn:Ep; [|rewrite Hp in Ep; discriminate].
lia.
Qed.
Lemma firstn_succ_last : forall (u : list Z) k, (k < length u)%nat ->
  firstn (S k) u = firstn k u ++ [ManifestModel.byte_at u k].
Proof.
intros u. induction u as [|c u IH]; intros k Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; cbn [firstn app]; [reflexivity|].
rewrite (IH k ltac:(lia)). reflexivity.
Qed.
Lemma forallb_firstn_step : forall (u : list Z) k, (0 < k)%nat -> (k <= length u)%nat ->
  forallb (fun c => negb (c =? 62)) (firstn (k - 1) u) = true ->
  ManifestModel.byte_at u (k - 1) <> 62 ->
  forallb (fun c => negb (c =? 62)) (firstn k u) = true.
Proof.
intros u k Hk0 Hk Hf Hb.
replace k with (S (k - 1)) by lia. rewrite (firstn_succ_last u (k - 1) ltac:(lia)).
rewrite forallb_app, Hf. cbn [forallb andb].
rewrite Bool.andb_true_r. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hb.
Qed.
Lemma rt_peak_idem : forall u live peak, rt_peak u live (rt_peak u live peak) = rt_peak u live peak.
Proof. intros u live peak. unfold rt_peak. destruct u as [|c u']; [reflexivity | lia]. Qed.
Lemma crt_peak_step : forall u live peak m,
  rt_peak u live (if m =? 0 then peak else rt_peak u live peak) = rt_peak u live peak.
Proof. intros u live peak m. destruct (Z.eqb_spec m 0); [reflexivity | apply rt_peak_idem]. Qed.
Lemma req_size_pos : forall n, 0 <= n -> 0 < req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma req_size_ge : forall n, 0 <= n -> n <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* ---- the output strings: lengths and no NUL ---- *)
Lemma split_len : forall (u : list Z) k, (k <= length u)%nat ->
  Z.of_nat (length (firstn k u)) + Z.of_nat (length (skipn k u)) = Z.of_nat (length u).
Proof. intros u k Hk. rewrite length_firstn, length_skipn. lia. Qed.
Lemma txt_len_whole : forall u, Z.of_nat (length (ManifestModel.txt_whole u)) = Z.of_nat (length u) + 22.
Proof.
intros u. unfold ManifestModel.txt_whole, ManifestModel.tail_lv2.
cbn [length]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma txt_len_wholex : forall u, Z.of_nat (length (ManifestModel.txt_wholex u)) = Z.of_nat (length u) + 23.
Proof.
intros u. unfold ManifestModel.txt_wholex, ManifestModel.tail_lv2.
cbn [length]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma txt_len_t1 : forall u k, (k <= length u)%nat ->
  Z.of_nat (length (ManifestModel.txt_t1 u k)) = Z.of_nat (length u) + 38.
Proof.
intros u k Hk. unfold ManifestModel.txt_t1, ManifestModel.tail_lv2.
rewrite !length_app. cbn [length]. pose proof (split_len u k Hk). lia.
Qed.
Lemma txt_len_t2 : forall u k, (k <= length u)%nat ->
  Z.of_nat (length (ManifestModel.txt_t2 u k)) = Z.of_nat (length u) + 35.
Proof.
intros u k Hk. unfold ManifestModel.txt_t2, ManifestModel.tail_lv2.
rewrite !length_app. cbn [length]. pose proof (split_len u k Hk). lia.
Qed.
Lemma txt_len_t3 : forall u k, (k <= length u)%nat ->
  Z.of_nat (length (ManifestModel.txt_t3 u k)) = Z.of_nat (length u) + 36.
Proof.
intros u k Hk. unfold ManifestModel.txt_t3, ManifestModel.tail_lv2.
rewrite !length_app. cbn [length]. pose proof (split_len u k Hk). lia.
Qed.
Lemma txt_len_t1x : forall u k, (k <= length u)%nat ->
  Z.of_nat (length (ManifestModel.txt_t1x u k)) = Z.of_nat (length u) + 39.
Proof.
intros u k Hk. unfold ManifestModel.txt_t1x, ManifestModel.tail_lv2.
rewrite !length_app. cbn [length]. pose proof (split_len u k Hk). lia.
Qed.
Lemma nz_txt_whole : forall u, Forall (fun c => c <> 0) u ->
  Forall (fun c => c <> 0) (ManifestModel.txt_whole u).
Proof.
intros u H. unfold ManifestModel.txt_whole, ManifestModel.tail_lv2.
apply Forall_cons; [lia|]. apply fa_app; [exact H | nzlist].
Qed.
Lemma nz_txt_wholex : forall u, Forall (fun c => c <> 0) u ->
  Forall (fun c => c <> 0) (ManifestModel.txt_wholex u).
Proof.
intros u H. unfold ManifestModel.txt_wholex, ManifestModel.tail_lv2.
apply Forall_cons; [lia|]. apply fa_app; [exact H | nzlist].
Qed.
Local Ltac nz_split H :=
  apply fa_app; [nzlist|]; apply fa_app; [apply nz_firstn; exact H|];
  apply fa_app; [nzlist|]; apply fa_app; [apply nz_skipn; exact H | nzlist].
Lemma nz_txt_t1 : forall u k, Forall (fun c => c <> 0) u ->
  Forall (fun c => c <> 0) (ManifestModel.txt_t1 u k).
Proof. intros u k H. unfold ManifestModel.txt_t1, ManifestModel.tail_lv2. nz_split H. Qed.
Lemma nz_txt_t2 : forall u k, Forall (fun c => c <> 0) u ->
  Forall (fun c => c <> 0) (ManifestModel.txt_t2 u k).
Proof. intros u k H. unfold ManifestModel.txt_t2, ManifestModel.tail_lv2. nz_split H. Qed.
Lemma nz_txt_t3 : forall u k, Forall (fun c => c <> 0) u ->
  Forall (fun c => c <> 0) (ManifestModel.txt_t3 u k).
Proof. intros u k H. unfold ManifestModel.txt_t3, ManifestModel.tail_lv2. nz_split H. Qed.
Lemma nz_txt_t1x : forall u k, Forall (fun c => c <> 0) u ->
  Forall (fun c => c <> 0) (ManifestModel.txt_t1x u k).
Proof. intros u k H. unfold ManifestModel.txt_t1x, ManifestModel.tail_lv2. nz_split H. Qed.

(* ---- the format pieces of fm's six check_round_trip formats (FMH_Rt.v FM_SN_FMTS) ---- *)
Definition ps_tw : list fpiece := [FLit [60]; FStr; FLit (62 :: ManifestModel.tail_lv2)].
Definition ps_tx : list fpiece := [FLit [60]; FStr; FLit (88 :: 62 :: ManifestModel.tail_lv2)].
Definition ps_t1 : list fpiece :=
  [FLit [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60]; FPStr; FLit [62; 32; 46; 10; 112; 58]; FStr;
   FLit ManifestModel.tail_lv2].
Definition ps_t2 : list fpiece :=
  [FLit [80; 82; 69; 70; 73; 88; 32; 112; 58; 32; 60]; FPStr; FLit [62; 10; 112; 58]; FStr;
   FLit ManifestModel.tail_lv2].
Definition ps_t3 : list fpiece :=
  [FLit [64; 112; 114; 101; 102; 105; 120; 32; 58; 32; 60]; FPStr; FLit [62; 32; 46; 10; 58]; FStr;
   FLit ManifestModel.tail_lv2].
Definition ps_t1x : list fpiece :=
  [FLit [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60]; FPStr; FLit [62; 32; 46; 10; 112; 58]; FStr;
   FLit (88 :: ManifestModel.tail_lv2)].
Lemma in_ps_tw : In (FMT_tw, ps_tw) FM_SN_FMTS.
Proof. cbv [FM_SN_FMTS]. right. left. reflexivity. Qed.
Lemma in_ps_tx : In (FMT_tx, ps_tx) FM_SN_FMTS.
Proof. cbv [FM_SN_FMTS]. right. right. left. reflexivity. Qed.
Lemma in_ps_t1 : In (FMT_t1, ps_t1) FM_SN_FMTS.
Proof. cbv [FM_SN_FMTS]. right. right. right. left. reflexivity. Qed.
Lemma in_ps_t2 : In (FMT_t2, ps_t2) FM_SN_FMTS.
Proof. cbv [FM_SN_FMTS]. right. right. right. right. left. reflexivity. Qed.
Lemma in_ps_t3 : In (FMT_t3, ps_t3) FM_SN_FMTS.
Proof. cbv [FM_SN_FMTS]. right. right. right. right. right. left. reflexivity. Qed.
Lemma in_ps_t1x : In (FMT_t1x, ps_t1x) FM_SN_FMTS.
Proof. cbv [FM_SN_FMTS]. right. right. right. right. right. right. left. reflexivity. Qed.

(* after a symbolic run: a register the run left as its entry atom; the frame of a run with no writable region *)
Ltac crt_keep HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = getr ?regs ?r' =>
    let z := eval vm_compute in (Z.to_nat (bv_unsigned r')) in
    exact (fmw_reg_atom _ regs _ _ ms r r' z HS ltac:(vm_compute; reflexivity) eq_refl) end.
Ltac crt_sb0 m1 m2 SB :=
  match goal with H : frame_of _ _ m1 m2 |- _ =>
    let H' := fresh "HF'" in pose proof H as H'; cbn [add_cond ss_mem fss_nr] in H';
    pose proof (frame_nil_same _ _ _ H') as SB; clear H' end.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis SNP : asnprintf_realizes tfibsegs B PC_snprintf.
Hypothesis MUSTNAME : must_name_spec B CTX_must_name.
Hypothesis ASR : as_ruled_spec tfibsegs B CTX_as_ruled.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- image ranges the walk must keep apart from its text buffer ---- *)
Lemma crt_img_of_b : forall lo hi a,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  lo <= a < hi -> in_img tfibsegs a.
Proof.
intros lo hi a Hb Ha. apply existsb_exists in Hb as (s & Hs & Hss).
apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
Lemma crt_ro_img : forall a, 0x20d00 <= a < 0x20fe8 -> in_img tfibsegs a.
Proof. intros a Ha. exact (crt_img_of_b 0x20d00 0x20fe8 a ltac:(vm_compute; reflexivity) Ha). Qed.
Lemma crt_canary_img : forall a, FM_canary <= a < FM_canary + 8 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold FM_canary in Ha.
exact (crt_img_of_b 0x5f50b0 0x5f50b8 a ltac:(vm_compute; reflexivity) Ha).
Qed.
Lemma crt_stat_img : forall g, In g [G_FAIL; G_LIVE; G_PEAK; G_COUNT] ->
  forall a, g <= a < g + 8 -> in_img tfibsegs a.
Proof.
intros g Hg a Ha. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Hg.
destruct Hg as [<-|[<-|[<-|[<-|[]]]]].
- exact (crt_img_of_b 0x9e260 0x9e268 a ltac:(vm_compute; reflexivity) Ha).
- exact (crt_img_of_b 0x5d4700 0x5d4708 a ltac:(vm_compute; reflexivity) Ha).
- exact (crt_img_of_b 0x5d4720 0x5d4728 a ltac:(vm_compute; reflexivity) Ha).
- exact (crt_img_of_b 0x5d4740 0x5d4748 a ltac:(vm_compute; reflexivity) Ha).
Qed.
(* every read-only string and format fm passes lives in [0x20d00, 0x20fe8) *)
Lemma crt_listed_range : forall p0 l0,
  (In (p0, l0) FM_RO_STRS \/ (exists ps, In (p0, ps) FM_SN_FMTS /\ l0 = fmt_bytes ps)) ->
  0x20d00 <= p0 /\ p0 + Z.of_nat (length l0) + 1 <= 0x20fe8.
Proof.
intros p0 l0 [Hro | (ps & Hps & ->)].
- cbv [FM_RO_STRS In STR_empty] in Hro.
  repeat (destruct Hro as [E|Hro]; [injection E as E1 E2; subst; cbn [length]; lia|]). destruct Hro.
- cbv [FM_SN_FMTS In FMT_whole FMT_tw FMT_tx FMT_t1 FMT_t2 FMT_t3 FMT_t1x] in Hps.
  repeat (destruct Hps as [E|Hps];
    [injection E as E1 E2; subst; vm_compute (Z.of_nat (length (fmt_bytes _))); lia|]).
  destruct Hps.
Qed.
(* a live block and an image range are apart *)
Lemma crt_blk_out : forall ly S (W : world tfibsegs) mem md b m lo hi,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
  (forall a, lo <= a < hi -> in_img tfibsegs a) -> lo < hi ->
  hi <= b \/ b + req_size m <= lo.
Proof.
intros ly S W mem md b m lo hi HAR Hin Himg Hlh.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos m ltac:(lia)) as Hq.
destruct (Z_le_gt_dec hi b) as [H1|H1]; [left; lia|].
destruct (Z_le_gt_dec (b + req_size m) lo) as [H2|H2]; [right; lia|].
exfalso. apply (blk_img tfibsegs B LAWS ly S W mem md b m (Z.max b lo) HAR Hin ltac:(lia)).
apply Himg. lia.
Qed.
Lemma crt_img_notin : forall ly S (W : world tfibsegs) mem md b m lo hi a,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
  (forall x, lo <= x < hi -> in_img tfibsegs x) -> lo <= a < hi -> ~ (b <= a < b + m).
Proof.
intros ly S W mem md b m lo hi a HAR Hin Himg Ha Hr.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_ge m ltac:(lia)).
apply (blk_img tfibsegs B LAWS ly S W mem md b m a HAR Hin ltac:(lia)). apply Himg. exact Ha.
Qed.
(* the text buffer is apart from every block the entry state held *)
Lemma crt_blk_sep : forall ly S (W : world tfibsegs) mem md t n bl0,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) ((t, n) :: bl0) ->
  forall b m, In (b, m) bl0 -> zdisjoint (t, req_size n) (b, req_size m).
Proof.
intros ly S W mem md t n bl0 HAR Hperm b m Hin.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _].
pose proof (Permutation_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) Hperm) as Hpm.
cbn [map fst snd] in Hpm.
assert (Hp' : pairwise zdisjoint ((t, req_size n) :: map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) bl0))
  by exact (pairwise_perm_zdisj _ _ Hpm Hp).
destruct Hp' as [HF _].
exact (proj1 (Forall_forall _ _) HF (b, req_size m)
  (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) bl0 (b, m) Hin)).
Qed.
Lemma crt_blk_new : forall ly S (W : world tfibsegs) mem md t n bl0,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) ((t, n) :: bl0) -> 0 < n ->
  ~ In (t, n) bl0.
Proof.
intros ly S W mem md t n bl0 HAR Hperm Hn Hin.
pose proof (crt_blk_sep ly S W mem md t n bl0 HAR Hperm t n Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos n ltac:(lia)). lia.
Qed.
(* the uri and the text buffer are apart *)
Lemma crt_uri_disj : forall cx ly S (W : world tfibsegs) mem md t n p l,
  AR tfibsegs B ly S W mem md ->
  Permutation (ablocks B ly S) ((t, n) :: ablocks B (cx_ly cx) (cx_S cx)) ->
  cstr_kept B (cx_ly cx) (cx_S cx) p l -> 0 < n ->
  p + Z.of_nat (length l) + 1 <= t \/ t + n <= p.
Proof.
intros cx ly S W mem md t n p l HAR Hperm Hk Hn.
assert (Hin : In (t, n) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct Hk as [(b & m & Hinb & Hb & Hbm) | (p0 & l0 & kk & Hlist & Hk0 & -> & ->)].
- pose proof (crt_blk_sep ly S W mem md t n _ HAR Hperm b m Hinb) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hm : 0 < m) by lia.
  assert (Hrm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  lia.
- destruct (crt_listed_range p0 l0 Hlist) as [Hlo Hhi].
  rewrite length_skipn.
  pose proof (crt_blk_out ly S W mem md t n 0x20d00 0x20fe8 HAR Hin crt_ro_img ltac:(lia)) as [H|H]; lia.
Qed.
Lemma crt_canary_disj : forall ly S (W : world tfibsegs) mem md t n d,
  AR tfibsegs B ly S W mem md -> In (t, n) (ablocks B ly S) -> 0 < n -> t <= d -> d <= t + n ->
  d <= FM_canary \/ FM_canary + 8 <= t.
Proof.
intros ly S W mem md t n d HAR Hin Hn Ht Hd.
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
pose proof (crt_blk_out ly S W mem md t n FM_canary (FM_canary + 8) HAR Hin crt_canary_img ltac:(lia)) as [H|H];
  [right; lia | left; lia].
Qed.

(* ---- facts that survive a write into the text buffer ---- *)
Lemma crt_glob_kept : forall ly S (W : world tfibsegs) mem md mem' t n live peak cnt fail (X : Z -> Prop),
  AR tfibsegs B ly S W mem md -> In (t, n) (ablocks B ly S) ->
  (forall a, X a -> (t <= a < t + n) \/ alloc_ceiling <= a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  fm_glob tfibsegs W mem live peak cnt fail -> fm_glob tfibsegs W mem' live peak cnt fail.
Proof.
intros ly S W mem md mem' t n live peak cnt fail X HAR Hin HX Heq (G1 & G2 & G3 & G4 & R).
pose proof asan_consts as (C1 & _).
assert (VB : forall g, In g [G_FAIL; G_LIVE; G_PEAK; G_COUNT] -> forall v,
  val_mem tfibsegs (rdW W mem) g 8 v -> val_mem tfibsegs (rdW W mem') g 8 v).
{ intros g Hg v Hv. eapply (val_mem_kept tfibsegs); [|exact Hv]. intros j Hj.
  assert (Hgr : 0x9e260 <= g <= 0x5d4740)
    by (unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Hg; destruct Hg as [<-|[<-|[<-|[<-|[]]]]]; lia).
  apply Heq; [cbn in Hj; lia|].
  intros HXa. destruct (HX _ HXa) as [Hb | Hc].
  - exact (crt_img_notin ly S W mem md t n g (g + 8) (g + j) HAR Hin (crt_stat_img g Hg)
      ltac:(cbn in Hj; lia) Hb).
  - cbn in Hj. lia. }
unfold fm_glob.
split; [apply (VB G_LIVE ltac:(right; left; reflexivity)); exact G1|].
split; [apply (VB G_PEAK ltac:(right; right; left; reflexivity)); exact G2|].
split; [apply (VB G_COUNT ltac:(right; right; right; left; reflexivity)); exact G3|].
split; [apply (VB G_FAIL ltac:(left; reflexivity)); exact G4|].
exact R.
Qed.
Lemma crt_aro_kept : forall ly S (W : world tfibsegs) mem md mem' t n (X : Z -> Prop),
  AR tfibsegs B ly S W mem md -> In (t, n) (ablocks B ly S) ->
  (forall a, X a -> (t <= a < t + n) \/ alloc_ceiling <= a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem').
Proof.
intros ly S W mem md mem' t n X HAR Hin HX Heq HR a Ha Ho He.
pose proof asan_consts as (C1 & _).
pose proof (roP_img a Ha) as Hi.
pose proof (fm_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
rewrite Heq; [exact (HR a Ha Ho He) | lia |].
intros HXa. destruct (HX a HXa) as [Hb | Hc]; [|lia].
destruct (al_blocks _ _ LAWS ly S W mem md t n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_ge n ltac:(lia)).
exact (blk_img tfibsegs B LAWS ly S W mem md t n a HAR Hin ltac:(lia) Hi).
Qed.
Lemma amem_of_app : forall p n, in_app p n -> amem_range p n.
Proof.
intros p n [H0 [HL | [HH1 HH2]]]; unfold amem_range.
- left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
- right. pose proof asan_consts as (C1 & _). unfold ASAN_CEIL, kHighMemEnd in *. lia.
Qed.
(* cstr_ok of a string that lives inside a live block whose bytes the walk knows *)
Lemma crt_cstr_ok_blk : forall ly S (W : world tfibsegs) mem md b m p l,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  b <= p -> p + Z.of_nat (length l) + 8 <= b + m ->
  garr8 tfibsegs (rdW W mem) p (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  Z.of_nat (length l) + 1 < 2 ^ 32 ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S W mem md b m p l HAR Hin Hm Hb Hbm Hg Hnz H32.
pose proof asan_consts as (C1 & _).
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & Happ & Hpres & _ & Hn).
rewrite Hrq in Hceil, Happ.
split; [split; [exact Hg | exact Hnz]|].
split; [lia|]. split; [lia|]. split; [exact H32|].
split; [apply amem_of_app; eapply in_app_sub; [exact Happ | lia | lia | lia]|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md b m p _ HAR Hin Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hhv').
  apply (shadow_hull_vis_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (block_word_tail_vis B LAWS ly S W mem md b m HAR Hin Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

(* ---- the core at a resume point, rebuilt from the journal ---- *)
Lemma crt_core_of : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k,
  crt_base B cx -> crt_J B cx ly' S' W' mem' md' k ->
  (forall x, In x (ablocks B (cx_ly cx) (cx_S cx)) -> In x (ablocks B ly' S')) ->
  crt_frame cx W' mem' ->
  spZ regs' = cx_sp0 cx - CRT_FRAME -> getr regs' 3 = getr (cx_regs cx) 3 -> getr regs' 4 = getr (cx_regs cx) 4 ->
  getr regs' 8 = w64 (cx_u cx) -> getr regs' 26 = w64 FMW_SB ->
  crt_core B cx ly' S' W' regs' mem' md' k.
Proof.
intros cx ly' S' W' regs' mem' md' k (HPRE & _ & _ & Hu & Hku & _) HJ Hinc HFR Hsp Hgp Htp Hs0 Hs10.
destruct HPRE as [HAP HRO].
assert (HRO' : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem'))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ pstat_closed pstat_not_roP HRO).
split; [exact HJ|]. split; [exact HFR|].
split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hs0|]. split; [exact Hs10|].
split; [exact (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IMG HJ Hinc pstat_img HRO' Hku Hu)|].
split; [exact (cstr_kept_kept B _ _ _ _ _ _ Hinc Hku)|].
exact HRO'.
Qed.
(* a stretch that touches no memory below the ceiling and keeps the walk's registers *)
Lemma crt_tcore_nr : forall cx ly S (W : world tfibsegs) regs mem md k t m regs' mem' md',
  crt_base B cx -> crt_tcore B cx ly S W regs mem md k t m ->
  crt_J B cx ly S W mem' md' k -> same_below mem mem' (2 ^ 64) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 26 = getr regs 26 ->
  crt_tcore B cx ly S W regs' mem' md' k t m.
Proof.
intros cx ly S W regs mem md k t m regs' mem' md' HB HT HJ' SB R2 R3 R4 R8 R9 R18 R26.
pose proof HT as ((HJ & HFR & Hsp & Hgp & Htp & Hs0 & Hs10 & Hcu & Hkpt & HRO) & Hk & Hn1 & H9 & H18 & Ht4096 & Hperm & HG).
pose proof asan_consts as (C1 & _).
unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
zval FS STK_check_round_trip.
assert (SBc : same_below mem mem' alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
assert (Hinc : forall x, In x (ablocks B (cx_ly cx) (cx_S cx)) -> In x (ablocks B ly S))
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hx).
split; [|split; [exact Hk | split; [exact Hn1|]]].
{ apply (crt_core_of cx ly S W regs' mem' md' k HB HJ' Hinc).
  - apply (crt_frame_below cx W mem mem' SB); [unfold CRT_FRAME; lia | lia | exact HFR].
  - unfold spZ. rewrite R2. exact Hsp.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite R8. exact Hs0.
  - rewrite R26. exact Hs10. }
split; [rewrite R9; exact H9|]. split; [rewrite R18; exact H18|].
split; [exact Ht4096|]. split; [exact Hperm|].
unfold crt_glob in HG |- *. exact (fm_glob_below W mem mem' _ _ _ _ SBc HG).
Qed.

(* ---- frender for fm's two format shapes ---- *)
Lemma frender_ls : forall (W : world tfibsegs) mem d sz a b p s rest out,
  cstr_ok tfibsegs W mem p s -> (p + Z.of_nat (length s) + 1 <= d \/ d + sz <= p) ->
  out = a ++ s ++ b ->
  frender tfibsegs W mem d sz [FLit a; FStr; FLit b] (p :: rest) out.
Proof.
intros W mem d sz a b p s rest out Hc Hd ->. cbn [frender].
exists (s ++ b). split; [reflexivity|].
exists s, b. split; [exact Hc|]. split; [exact Hd|]. split; [reflexivity|].
exists []. split; [symmetry; apply app_nil_r | reflexivity].
Qed.
Lemma frender_lplsl : forall (W : world tfibsegs) mem d sz a b c kz p s p2 s2 rest out,
  1 <= kz <= Z.of_nat (length s) -> cstr_ok tfibsegs W mem p s ->
  (p + Z.of_nat (length s) + 1 <= d \/ d + sz <= p) ->
  cstr_ok tfibsegs W mem p2 s2 -> (p2 + Z.of_nat (length s2) + 1 <= d \/ d + sz <= p2) ->
  out = a ++ firstn (Z.to_nat kz) s ++ b ++ s2 ++ c ->
  frender tfibsegs W mem d sz [FLit a; FPStr; FLit b; FStr; FLit c] (kz :: p :: p2 :: rest) out.
Proof.
intros W mem d sz a b c kz p s p2 s2 rest out Hk Hc Hd Hc2 Hd2 ->. cbn [frender].
exists (firstn (Z.to_nat kz) s ++ b ++ s2 ++ c). split; [reflexivity|].
exists s, (b ++ s2 ++ c). split; [exact Hk|]. split; [exact Hc|]. split; [exact Hd|]. split; [reflexivity|].
exists (s2 ++ c). split; [reflexivity|].
exists s2, c. split; [exact Hc2|]. split; [exact Hd2|]. split; [reflexivity|].
exists []. split; [symmetry; apply app_nil_r | reflexivity].
Qed.

(* ---- the snprintf call of a pair: dest = the text buffer, size = its size ---- *)
Lemma crt_snp : forall cx ly S (W : world tfibsegs) regs mem md k t m (rr : Z) ps f out
    (Q : world tfibsegs -> config -> Prop),
  crt_base B cx -> crt_tcore B cx ly S W regs mem md k t m ->
  getr regs 1 = Z_to_bv 64 rr -> 4096 <= rr < 2 ^ 64 -> rr mod 2 = 0 ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (crt_tsz (cx_n cx)) -> getr regs 12 = w64 f ->
  In (f, ps) FM_SN_FMTS ->
  frender tfibsegs W mem t (crt_tsz (cx_n cx)) ps
    (map (fun r : Z => bv_unsigned (getr regs (Z_to_bv 5 r))) [13; 14; 15; 16; 17]) out ->
  Z.of_nat (length out) + 8 <= crt_tsz (cx_n cx) -> Forall (fun c => c <> 0) out ->
  (forall regs' mem' md',
     crt_tcore B cx ly S W regs' mem' md' k t m -> aregs_preserved regs regs' ->
     cstr_ok tfibsegs W mem' t out ->
     (forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W (cfg_at tfibsegs rr regs' mem' md') Q) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_snprintf regs mem md) Q.
Proof.
intros cx ly S W regs mem md k t m rr ps f out Q HB HT Hra Hrr0 Hrr2 H10 H11 H12 Hf Hfr Hlen Hnz K.
pose proof HT as ((HJ & HFR & Hsp & Hgp & Htp & Hs0 & Hs10 & Hcu & Hkpt & HRO) & Hk & Hn1 & H9 & H18 & Ht4096 & Hperm & HG).
pose proof HB as (HPRE0 & _ & _ & Hu0 & Hku0 & Hlu & HG0 & HQ & Hlive & Hev & Hbb).
pose proof asan_consts as (C1 & _).
unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
zval FS STK_check_round_trip.
zval FP STK_RT_PRINTF.
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
assert (Hnle : crt_tsz (cx_n cx) <= 829) by (unfold crt_tsz, cx_n; lia).
assert (Hin : In (t, crt_tsz (cx_n cx)) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hrq : req_size (crt_tsz (cx_n cx)) = crt_tsz (cx_n cx))
  by (unfold req_size; destruct (Z.eqb_spec (crt_tsz (cx_n cx)) 0); lia).
destruct (al_blocks _ _ LAWS ly S W mem md t (crt_tsz (cx_n cx)) HAR Hin)
  as (Hal & H4096 & Hbceil & Happ & Hpa & _ & Hnmax).
rewrite Hrq in Hbceil, Happ, Hpa.
destruct (IMG ly S W mem md HAR HRO) as (HROM & _ & HCAN & _ & HFMT).
assert (Hspc : spZ regs = cx_sp0 cx + -112) by (unfold CRT_FRAME in Hsp; lia).
pose proof (fmw_ecall_pre_k B STK_check_round_trip (cx_sp0 cx) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
  (cx_mem cx) (cx_md cx) [] ly S W mem md k regs STK_RT_PRINTF (-112) HJ Hspc
  ltac:(reflexivity) ltac:(lia) ltac:(cbv [ESTACK]; lia) ltac:(lia)
  ltac:(rewrite Hra; apply ret_ok_even; rewrite unsigned_lit_small by lia; lia)
  ltac:(rewrite Hgp; exact (proj1 (proj2 (proj2 (proj2 (proj1 HPRE0))))))
  ltac:(rewrite Htp; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HPRE0)))))))) as HEC.
destruct HEC as (HE & HE2 & HE3 & HE4).
eapply SRr_bind.
{ apply (SNP ly S [] W regs mem md t (crt_tsz (cx_n cx)) f ps out).
  - split; [|split; [exact HE2 | split; [exact HE3 | exact HE4]]].
    apply (proj2 (ecall_preU_nil tfibsegs B ly S W regs mem md)). exact HE.
  - exact HROM.
  - exact HCAN.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact Hf.
  - exact (proj1 (HFMT f ps Hf)).
  - exact Hfr.
  - split; lia.
  - split; [lia|]. split; [lia|].
    split; [apply amem_of_app; eapply in_app_sub; [exact Happ | lia | lia | lia]|].
    split.
    { intros a Ha. destruct (Hpa a ltac:(lia)) as [Hp Ho].
      split; [exact (apresent_writable tfibsegs _ _ _ Hp)|]. split; [exact Ho | lia]. }
    split.
    { apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md t (crt_tsz (cx_n cx)) t _ HAR Hin
        ltac:(lia)). rewrite Hrq. lia. }
    intros _. destruct (al_shadow _ _ LAWS ly S W mem md t (crt_tsz (cx_n cx)) HAR Hin) as (_ & Hhv).
    apply (shadow_hull_vis_sub _ t (req_size (crt_tsz (cx_n cx))) t _ Hhv ltac:(lia)); rewrite ?Hrq; lia.
  - exact (crt_canary_disj ly S W mem md t (crt_tsz (cx_n cx)) (t + Z.of_nat (length out) + 1)
      HAR Hin Hnpos ltac:(lia) ltac:(lia)).
  - lia.
  - intros a Ha (sg & Hsg & _ & Hr).
    apply (blk_img tfibsegs B LAWS ly S W mem md t (crt_tsz (cx_n cx)) a HAR Hin ltac:(rewrite Hrq; lia)).
    exists sg. split; [exact Hsg | exact Hr]. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & _ & HP2 & Hsame2 & H10r & Hbytes & Hfrm & Hgr).
rewrite unpoison_nil in HAR2.
assert (Hfrm' : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((t <= a < t + Z.of_nat (length out) + 1) \/ (spZ regs - STK_RT_PRINTF <= a < spZ regs)) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha HnW; apply Hfrm; [lia | tauto | tauto]).
assert (HJ2 : crt_J B cx ly S W mem2 md2 k).
{ unfold crt_J.
  eapply (ajournal_after_write tfibsegs B LAWS fm_segs_low STK_check_round_trip (cx_sp0 cx) FM_PSTAT_FP
    (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) [] ly S W mem md k mem2 md2
    (fun a => (t <= a < t + Z.of_nat (length out) + 1) \/ (spZ regs - STK_RT_PRINTF <= a < spZ regs)) S []).
  - exact HJ.
  - exact Hfrm'.
  - exact Hgr.
  - exact Hsame2.
  - intros a [Ha | Ha]; left; left.
    + right. right. left. exists t, (crt_tsz (cx_n cx)). split; [exact Hin|].
      split; [exact (crt_blk_new ly S W mem md t (crt_tsz (cx_n cx)) _ HAR Hperm Hnpos) | rewrite Hrq; lia].
    + left. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
assert (Hkeep : forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. unfold CRT_FRAME in Ha. apply Hfrm'; [lia | lia]. }
assert (HX : forall a, ((t <= a < t + Z.of_nat (length out) + 1) \/
    (spZ regs - STK_RT_PRINTF <= a < spZ regs)) ->
  (t <= a < t + crt_tsz (cx_n cx)) \/ alloc_ceiling <= a)
  by (intros a [Ha | Ha]; [left; lia | right; lia]).
assert (HFR2 : crt_frame cx W mem2).
{ apply (crt_frame_kept cx W W mem mem2); [|exact HFR]. intros a Ha. apply Hkeep. lia. }
assert (HG2 : crt_glob cx W mem2 m).
{ unfold crt_glob in HG |- *.
  exact (crt_glob_kept ly S W mem md mem2 t (crt_tsz (cx_n cx)) _ _ _ _ _ HAR Hin HX Hfrm' HG). }
assert (Hinc : forall x, In x (ablocks B (cx_ly cx) (cx_S cx)) -> In x (ablocks B ly S))
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hx).
assert (HT2 : crt_tcore B cx ly S W regs2 mem2 md2 k t m).
{ split; [|split; [exact Hk | split; [exact Hn1|]]].
  { apply (crt_core_of cx ly S W regs2 mem2 md2 k HB HJ2 Hinc HFR2).
    - unfold spZ. rewrite (fmw_pres _ _ 2%bv HP2 ltac:(cs_tac)). exact Hsp.
    - rewrite (fmw_pres _ _ 3%bv HP2 ltac:(cs_tac)). exact Hgp.
    - rewrite (fmw_pres _ _ 4%bv HP2 ltac:(cs_tac)). exact Htp.
    - rewrite (fmw_pres _ _ 8%bv HP2 ltac:(cs_tac)). exact Hs0.
    - rewrite (fmw_pres _ _ 26%bv HP2 ltac:(cs_tac)). exact Hs10. }
  split; [rewrite (fmw_pres _ _ 9%bv HP2 ltac:(cs_tac)); exact H9|].
  split; [rewrite (fmw_pres _ _ 18%bv HP2 ltac:(cs_tac)); exact H18|].
  split; [exact Ht4096|]. split; [exact Hperm | exact HG2]. }
assert (Hout : cstr_ok tfibsegs W mem2 t out).
{ apply (crt_cstr_ok_blk ly S W mem2 md2 t (crt_tsz (cx_n cx)) t out HAR2 Hin Hnpos ltac:(lia)
    ltac:(lia) Hbytes Hnz ltac:(lia)). }
unfold raZ. rewrite Hra, unsigned_lit_small by lia.
exact (K regs2 mem2 md2 HT2 HP2 Hout Hkeep).
Qed.

(* ---- a reader call of a pair ---- *)
Lemma crt_tcore_call : forall cx ly S (W : world tfibsegs) regs mem md k t m m' STKc ly2 S2 (W2 : world tfibsegs)
    regs2 mem2 md2 kc,
  crt_base B cx -> crt_tcore B cx ly S W regs mem md k t m ->
  ajournal tfibsegs B STKc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 mem2 md2 kc ->
  aregs_preserved regs regs2 -> STKc <= STK_as_ruled ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  0 <= k + kc <= 1 + 2 * m' -> crt_glob cx W2 mem2 m' ->
  crt_tcore B cx ly2 S2 W2 regs2 mem2 md2 (k + kc) t m' /\
  (forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
     aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) mem a).
Proof.
intros cx ly S W regs mem md k t m m' STKc ly2 S2 W2 regs2 mem2 md2 kc HB HT HJc HP Hstkc Hperm2 Hk2 HG2.
pose proof HT as ((HJ & HFR & Hsp & Hgp & Htp & Hs0 & Hs10 & Hcu & Hkpt & HRO) & Hk & Hn1 & H9 & H18 & Ht4096 & Hperm & HG).
pose proof asan_consts as (C1 & _).
unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
zval FS STK_check_round_trip. zval FA STK_as_ruled.
assert (HJ2 : crt_J B cx ly2 S2 W2 mem2 md2 (k + kc)).
{ unfold crt_J.
  pose proof (ajournal_sub_incl B STK_check_round_trip (cx_sp0 cx) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
    (cx_mem cx) (cx_md cx) [] ly S W mem md k STKc (spZ regs) FM_PSTAT_FP [] ly2 S2 W2 mem2 md2 kc HJ HJc
    ltac:(rewrite Hsp; unfold CRT_FRAME; lia) ltac:(rewrite Hsp; unfold CRT_FRAME; lia)
    (fun a Ha => Ha)) as H.
  cbn [app] in H. exact H. }
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (Hkeep : forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. apply F1c; [unfold CRT_FRAME in Ha; lia | rewrite Hsp; unfold CRT_FRAME in *; lia]. }
assert (HFR2 : crt_frame cx W2 mem2).
{ apply (crt_frame_kept cx W W2 mem mem2); [|exact HFR]. intros a Ha. apply Hkeep. lia. }
assert (Hinc : forall x, In x (ablocks B (cx_ly cx) (cx_S cx)) -> In x (ablocks B ly2 S2)).
{ intros x Hx. apply (Permutation_in _ (Permutation_sym Hperm2)).
  apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hx. }
split; [|exact Hkeep].
split; [|split; [exact Hk2 | split; [exact Hn1|]]].
{ apply (crt_core_of cx ly2 S2 W2 regs2 mem2 md2 (k + kc) HB HJ2 Hinc HFR2).
  - unfold spZ. rewrite (fmw_pres _ _ 2%bv HP ltac:(cs_tac)). exact Hsp.
  - rewrite (fmw_pres _ _ 3%bv HP ltac:(cs_tac)). exact Hgp.
  - rewrite (fmw_pres _ _ 4%bv HP ltac:(cs_tac)). exact Htp.
  - rewrite (fmw_pres _ _ 8%bv HP ltac:(cs_tac)). exact Hs0.
  - rewrite (fmw_pres _ _ 26%bv HP ltac:(cs_tac)). exact Hs10. }
split; [rewrite (fmw_pres _ _ 9%bv HP ltac:(cs_tac)); exact H9|].
split; [rewrite (fmw_pres _ _ 18%bv HP ltac:(cs_tac)); exact H18|].
split; [exact Ht4096|].
split; [exact (Permutation_trans Hperm2 Hperm) | exact HG2].
Qed.

Lemma crt_reader_pre : forall cx ly S (W : world tfibsegs) regs mem md k t m tb,
  crt_base B cx -> crt_tcore B cx ly S W regs mem md k t m -> m + 1 <= 3 + 4 * 254 ->
  cstr_ok tfibsegs W mem t tb -> Z.of_nat (length tb) + 1 <= crt_tsz (cx_n cx) ->
  cstr_kept B ly S t tb /\ Z.of_nat (length tb) <= MANIFEST_MAX /\
  cstr_ok tfibsegs W mem (cx_u cx) (cx_ub cx) /\ cstr_kept B ly S (cx_u cx) (cx_ub cx) /\
  (length (cx_ub cx) <= 255)%nat /\ quiet (cx_cnt cx + m) SIZE_MAXZ 1 /\
  cx_live cx + Z.of_nat (length (cx_ub cx)) + 3 < 2 ^ 33.
Proof.
intros cx ly S W regs mem md k t m tb HB HT Hm Hok Hlen.
pose proof HT as ((HJ & _ & _ & _ & _ & _ & _ & Hcu & Hkpt & _) & Hk & Hn1 & H9 & H18 & Ht4096 & Hperm & HG).
pose proof HB as (_ & _ & _ & _ & _ & Hlu & _ & HQ & Hlive & _).
assert (Hin : In (t, crt_tsz (cx_n cx)) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hnle : crt_tsz (cx_n cx) <= 829) by (unfold crt_tsz, cx_n; lia).
split; [left; exists t, (crt_tsz (cx_n cx)); split; [exact Hin | lia]|].
split; [unfold MANIFEST_MAX; lia|].
split; [exact Hcu|]. split; [exact Hkpt|]. split; [unfold cx_n in Hn1; exact Hlu|].
destruct HQ as (Hf & Hc0 & Hc1).
split; [split; [reflexivity | lia]|].
unfold cx_n in Hlive. lia.
Qed.

(* must_name (t, uri) (B 0x81a9c): names (t, uri), then the abort unless it answers 1; the caller knows the rule's
   answer is 1, so must_name returns with a0 = 1 *)
Lemma crt_mn_call : forall cx ly S (W : world tfibsegs) regs mem md k t m (rr : Z) tb
    (Q : world tfibsegs -> config -> Prop),
  crt_base B cx -> crt_tcore B cx ly S W regs mem md k t m ->
  getr regs 1 = Z_to_bv 64 rr -> 4096 <= rr < 2 ^ 64 -> rr mod 2 = 0 ->
  In [rr] CTX_must_name ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (cx_u cx) ->
  cstr_ok tfibsegs W mem t tb -> Z.of_nat (length tb) + 1 <= crt_tsz (cx_n cx) ->
  ManifestModel.names tb (cx_ub cx) = 1 ->
  m + 1 <= 3 + 4 * 254 -> k + EV_names <= 1 + 2 * (m + 1) ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2,
     crt_tcore B cx ly2 S2 W2 regs2 mem2 md2 (k + EV_names) t (m + 1) -> aregs_preserved regs regs2 ->
     getr regs2 10 = w64 1 ->
     (forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
        aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W2 (cfg_at tfibsegs rr regs2 mem2 md2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_must_name regs mem md) Q.
Proof.
intros cx ly S W regs mem md k t m rr tb Q HB HT Hra Hrr0 Hrr2 HCTX H10 H11 Hok Hlen Hnm Hm Hkev K.
pose proof HT as ((HJ & HFR & Hsp & Hgp & Htp & Hs0 & Hs10 & Hcu & Hkpt & HRO) & Hk & Hn1 & H9 & H18 & Ht4096 & Hperm & HG).
pose proof HB as (HPRE0 & _ & _ & Hu0 & Hku0 & Hlu & HG0 & HQ & Hlive & Hev & Hbb).
pose proof asan_consts as (C1 & _).
unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (crt_reader_pre cx ly S W regs mem md k t m tb HB HT Hm Hok Hlen)
  as (Hktb & Hmm & Hcu' & Hkpt' & Hlu' & Hq & Hlive').
zval FS STK_check_round_trip. zval FM STK_must_name.
assert (Hspc : spZ regs = cx_sp0 cx + -112) by (unfold CRT_FRAME in Hsp; lia).
assert (Hin : In (t, crt_tsz (cx_n cx)) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hnle : crt_tsz (cx_n cx) <= 829) by (unfold crt_tsz, cx_n; lia).
assert (Hbb2 : blocks_bytes S = crt_tsz (cx_n cx) + blocks_bytes (cx_S cx)).
{ rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), bsum_cons,
    <- (blocks_bytes_bsum B (cx_ly cx) (cx_S cx)). cbn [snd]. reflexivity. }
assert (Hne : (length (cx_ub cx) =? 0)%nat = false)
  by (apply Nat.eqb_neq; unfold cx_n in Hn1; lia).
eapply SRr_bind.
{ apply (MUSTNAME ly S W regs mem md [] t (cx_u cx) tb (cx_ub cx) (cx_live cx)
    (if m =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx)) (cx_cnt cx + m) SIZE_MAXZ).
  - split; [|exact HRO].
    apply (afn_pre_at tfibsegs B STK_check_round_trip (cx_sp0 cx) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
      (cx_mem cx) (cx_md cx) [] ly S W mem md k regs STK_must_name (-112) [] HJ Hspc).
    all: first [ reflexivity | lia
               | (rewrite Hra; apply ret_ok_even; rewrite unsigned_lit_small by lia; lia)
               | (unfold raZ; rewrite Hra, unsigned_lit_small by lia; lia)
               | (rewrite Hgp; exact (proj1 (proj2 (proj2 (proj2 (proj1 HPRE0))))))
               | (rewrite Htp; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HPRE0)))))))
               | (apply achain_low; unfold s0Z; rewrite Hs0; unfold w64;
                  destruct Hcu as (_ & H4096c & Hcc & _); rewrite unsigned_lit_small by lia; lia) ].
  - unfold raZ. rewrite Hra, unsigned_lit_small by lia. cbn [spine]. exact HCTX.
  - exact H10.
  - exact H11.
  - exact Hok.
  - exact Hcu'.
  - exact Hktb.
  - exact Hkpt'.
  - exact Hlu'.
  - exact Hmm.
  - exact HG.
  - exact Hlive'.
  - destruct Hq as (_ & Hc0 & Hc1). lia.
  - unfold EV_check_round_trip, EV_names in *. lia.
  - unfold LIVE_names, LIVE_check_round_trip in *. lia.
  - intros E. rewrite E in Hne. cbn in Hne. discriminate Hne.
  - destruct Hq as (_ & Hc0 & Hc1). unfold SIZE_MAXZ. lia.
  - exact Hnm. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & H10r & Hperm2 & HNR).
destruct (names_res_quiet W2 mem2 tb (cx_ub cx) (cx_live cx) _ (cx_cnt cx + m) SIZE_MAXZ 1 HNR Hq)
  as [_ HG2].
rewrite Hne in HG2. rewrite (crt_peak_step (cx_ub cx) (cx_live cx) (cx_peak cx) m) in HG2.
assert (HGn : crt_glob cx W2 mem2 (m + 1)).
{ unfold crt_glob.
  replace (if m + 1 =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx))
    with (rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx))
    by (destruct (Z.eqb_spec (m + 1) 0); [lia | reflexivity]).
  replace (cx_cnt cx + (m + 1)) with (cx_cnt cx + m + 1) by lia.
  exact HG2. }
destruct (crt_tcore_call cx ly S W regs mem md k t m (m + 1) STK_must_name ly2 S2 W2 regs2 mem2 md2 EV_names
  HB HT ltac:(exact HJc) HP2 STK_must_name_le_as_ruled Hperm2 ltac:(unfold EV_names in *; lia) HGn) as [HT2 Hkeep].
rewrite Hra.
change (mkCfg (mkst regs2 (Z_to_bv 64 rr) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs rr regs2 mem2 md2).
exact (K ly2 S2 W2 regs2 mem2 md2 HT2 HP2 H10r Hkeep).
Qed.

Lemma crt_asr_call : forall cx ly S (W : world tfibsegs) regs mem md k t m (rr : Z) tb
    (Q : world tfibsegs -> config -> Prop),
  crt_base B cx -> crt_tcore B cx ly S W regs mem md k t m ->
  getr regs 1 = Z_to_bv 64 rr -> 4096 <= rr < 2 ^ 64 -> rr mod 2 = 0 -> In [rr] CTX_as_ruled ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (cx_u cx) ->
  cstr_ok tfibsegs W mem t tb -> Z.of_nat (length tb) + 1 <= crt_tsz (cx_n cx) ->
  m + 1 <= 3 + 4 * 254 -> k + EV_as_ruled <= 1 + 2 * (m + 1) ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2,
     crt_tcore B cx ly2 S2 W2 regs2 mem2 md2 (k + EV_as_ruled) t (m + 1) -> aregs_preserved regs regs2 ->
     (forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
        aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W2 (cfg_at tfibsegs rr regs2 mem2 md2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_as_ruled regs mem md) Q.
Proof.
intros cx ly S W regs mem md k t m rr tb Q HB HT Hra Hrr0 Hrr2 HCTX H10 H11 Hok Hlen Hm Hkev K.
pose proof HT as ((HJ & HFR & Hsp & Hgp & Htp & Hs0 & Hs10 & Hcu & Hkpt & HRO) & Hk & Hn1 & H9 & H18 & Ht4096 & Hperm & HG).
pose proof HB as (HPRE0 & _ & _ & Hu0 & Hku0 & Hlu & HG0 & HQ & Hlive & Hev & Hbb).
pose proof asan_consts as (C1 & _).
unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (crt_reader_pre cx ly S W regs mem md k t m tb HB HT Hm Hok Hlen)
  as (Hktb & Hmm & Hcu' & Hkpt' & Hlu' & Hq & Hlive').
zval FS STK_check_round_trip. zval FA STK_as_ruled.
assert (Hspc : spZ regs = cx_sp0 cx + -112) by (unfold CRT_FRAME in Hsp; lia).
assert (Hin : In (t, crt_tsz (cx_n cx)) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hnle : crt_tsz (cx_n cx) <= 829) by (unfold crt_tsz, cx_n; lia).
assert (Hbb2 : blocks_bytes S = crt_tsz (cx_n cx) + blocks_bytes (cx_S cx)).
{ rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), bsum_cons,
    <- (blocks_bytes_bsum B (cx_ly cx) (cx_S cx)). cbn [snd]. reflexivity. }
assert (Hne : (length (cx_ub cx) =? 0)%nat = false)
  by (apply Nat.eqb_neq; unfold cx_n in Hn1; lia).
eapply SRr_bind.
{ apply (ASR ly S W regs mem md [] t (cx_u cx) tb (cx_ub cx) (cx_live cx)
    (if m =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx)) (cx_cnt cx + m) SIZE_MAXZ).
  - split; [|exact HRO].
    apply (afn_pre_at tfibsegs B STK_check_round_trip (cx_sp0 cx) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
      (cx_mem cx) (cx_md cx) [] ly S W mem md k regs STK_as_ruled (-112) [] HJ Hspc).
    all: first [ reflexivity | lia
               | (rewrite Hra; apply ret_ok_even; rewrite unsigned_lit_small by lia; lia)
               | (unfold raZ; rewrite Hra, unsigned_lit_small by lia; lia)
               | (rewrite Hgp; exact (proj1 (proj2 (proj2 (proj2 (proj1 HPRE0))))))
               | (rewrite Htp; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HPRE0)))))))
               | (apply achain_low; unfold s0Z; rewrite Hs0; unfold w64;
                  destruct Hcu as (_ & H4096c & Hcc & _); rewrite unsigned_lit_small by lia; lia) ].
  - unfold raZ. rewrite Hra, unsigned_lit_small by lia. cbn [spine]. exact HCTX.
  - exact H10.
  - exact H11.
  - exact Hok.
  - exact Hcu'.
  - exact Hktb.
  - exact Hkpt'.
  - exact Hlu'.
  - exact Hmm.
  - exact HG.
  - exact Hq.
  - exact Hlive'.
  - unfold EV_check_round_trip, EV_as_ruled, EV_names in *. lia.
  - unfold LIVE_as_ruled, LIVE_names, LIVE_check_round_trip in *. lia. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & Hperm2 & HG2).
rewrite Hne in HG2. rewrite (crt_peak_step (cx_ub cx) (cx_live cx) (cx_peak cx) m) in HG2.
assert (HGn : crt_glob cx W2 mem2 (m + 1)).
{ unfold crt_glob.
  replace (if m + 1 =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx))
    with (rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx))
    by (destruct (Z.eqb_spec (m + 1) 0); [lia | reflexivity]).
  replace (cx_cnt cx + (m + 1)) with (cx_cnt cx + m + 1) by lia.
  exact HG2. }
destruct (crt_tcore_call cx ly S W regs mem md k t m (m + 1) STK_as_ruled ly2 S2 W2 regs2 mem2 md2 EV_as_ruled
  HB HT ltac:(exact HJc) HP2 ltac:(lia) Hperm2 ltac:(unfold EV_as_ruled, EV_names in *; lia) HGn)
  as [HT2 Hkeep].
rewrite Hra.
change (mkCfg (mkst regs2 (Z_to_bv 64 rr) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs rr regs2 mem2 md2).
exact (K ly2 S2 W2 regs2 mem2 md2 HT2 HP2 Hkeep).
Qed.

(* ---- crt_segC1: CRT_P3 (0x8107c): a2 := tw; snprintf (t, 3 n + 64, tw, uri) at 0x81090; must_name (t, uri) at
   0x8109c (names answers 1, ManifestModel.rt_whole, so a0 = 1); back at CRT_P5 (fuzz_manifest.c:270-271) ---- *)
Lemma crt_segC1 : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k t,
  crt_base B cx -> crt_P3 B cx ly' S' W' regs' mem' md' k t ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 k2, crt_P5 B cx ly2 S2 W2 regs2 mem2 md2 k2 t ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_P5 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_P3 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k t HB (HT & H10 & H19) K5.
pose proof (AR_laws_ok tfibsegs B) as LAWS'. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & _ & Hku0 & Hlu & _).
pose proof HT as ((HJ & _ & _ & _ & _ & Hs0 & _ & Hcu & _ & _) & Hk & Hn1 & H9 & H18 & _ & Hperm & _).
assert (Hne : length (cx_ub cx) <> 0%nat) by (unfold cx_n in Hn1; lia).
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
assert (Hu64 : 0 <= cx_u cx < 2 ^ 64) by (destruct Hcu as (_ & Hu1 & Hu2 & _); lia).
(* the stretch to snprintf *)
pose proof (fmw_resume_nr W regs [] mem CRT_P3) as HS.
unfold crt_J in HJ.
unfold cfg_at. change (w64 CRT_P3) with (Z_to_bv 64 CRT_P3).
aj_run_to fmw_tbl_crt_ok HS HJ PC_snprintf.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
set (E1 := Ereg regs []) in HS.
crt_sb0 mem (ms_mem ms1) SB1.
pose proof (fmw_reg_lit _ E1 _ ms1 1%bv CRT_P4 HS ltac:(vm_compute; reflexivity) ltac:(unfold CRT_P4; lia)) as R1.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs _ _ ms1 11%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as R11.
pose proof (fmw_reg_lit _ E1 _ ms1 12%bv FMT_tw HS ltac:(vm_compute; reflexivity) ltac:(unfold FMT_tw; lia)) as R12.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 13) 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R13.
pose proof (fmw_reg_atom _ regs _ _ ms1 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as R19.
assert (HT1 : crt_tcore B cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k t 1).
{ apply (crt_tcore_nr cx ly S W regs mem md k t 1 (ms_regs ms1) (ms_mem ms1) md1 HB HT HJ SB1); crt_keep HS. }
pose proof HT1 as ((HJ1 & _ & _ & _ & _ & _ & _ & Hcu1 & _ & _) & _).
pose proof HJ1 as (HAR1 & _).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HS eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_snprintf) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs PC_snprintf (ms_regs ms1) (ms_mem ms1) md1).
apply (crt_snp cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k t 1 CRT_P4 ps_tw FMT_tw
  (ManifestModel.txt_whole (cx_ub cx)) _ HB HT1 R1).
- unfold CRT_P4; lia.
- reflexivity.
- rewrite R10. exact H18.
- rewrite R11. exact H9.
- rewrite R12. reflexivity.
- exact in_ps_tw.
- cbn [map]. rewrite R13, Hs0. unfold w64. rewrite (unsigned_lit_small (cx_u cx) Hu64).
  unfold ps_tw. apply (frender_ls W (ms_mem ms1) t _ [60] (62 :: ManifestModel.tail_lv2) (cx_u cx) (cx_ub cx)).
  + exact Hcu1.
  + exact (crt_uri_disj cx ly S W (ms_mem ms1) md1 t (crt_tsz (cx_n cx)) (cx_u cx) (cx_ub cx) HAR1 Hperm Hku0 Hnpos).
  + reflexivity.
- rewrite txt_len_whole. unfold crt_tsz, cx_n. lia.
- apply nz_txt_whole. exact (proj2 (proj1 Hcu)).
- intros regs2 mem2 md2 HT2 HP2 Hout2 _.
  pose proof HT2 as ((HJ2 & _ & _ & _ & _ & Hs02 & _ & _ & _ & _) & _ & _ & _ & H182 & _).
  (* the stretch to must_name: a0 := s2, a1 := s0 *)
  pose proof (fmw_resume_nr W regs2 [] mem2 CRT_P4) as HS2.
  unfold crt_J in HJ2.
  unfold cfg_at. change (w64 CRT_P4) with (Z_to_bv 64 CRT_P4).
  aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_must_name.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3 := mdx) in * end.
  set (E3 := Ereg regs2 []) in HS2.
  crt_sb0 mem2 (ms_mem ms3) SB3.
  pose proof (fmw_reg_lit _ E3 _ ms3 1%bv CRT_P5 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_P5; lia)) as Q1.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 10%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  assert (HT3 : crt_tcore B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k t 1).
  { apply (crt_tcore_nr cx ly S W regs2 mem2 md2 k t 1 (ms_regs ms3) (ms_mem ms3) md3 HB HT2 HJ2 SB3);
      crt_keep HS2. }
  assert (Hout3 : cstr_ok tfibsegs W (ms_mem ms3) t (ManifestModel.txt_whole (cx_ub cx))).
  { apply (cstr_ok_below W mem2 (ms_mem ms3)); [apply (same_below_mono _ _ _ _ SB3); lia | exact Hout2]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_must_name) (ms_mem ms3) (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs A_must_name (ms_regs ms3) (ms_mem ms3) md3).
  apply (crt_mn_call cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k t 1 CRT_P5
    (ManifestModel.txt_whole (cx_ub cx)) _ HB HT3 Q1).
  + unfold CRT_P5; lia.
  + reflexivity.
  + cbv [CTX_must_name CRT_P5]. repeat (first [left; reflexivity | right]).
  + rewrite Q10. exact H182.
  + rewrite Q11. exact Hs02.
  + exact Hout3.
  + rewrite txt_len_whole. unfold crt_tsz, cx_n. lia.
  + exact (ManifestModel.rt_whole (cx_ub cx) Hne).
  + lia.
  + unfold EV_names. lia.
  + intros ly4 S4 W4 regs4 mem4 md4 HT4 HP4 H10' _.
    apply (K5 ly4 S4 W4 regs4 mem4 md4 (k + EV_names)).
    split; [exact HT4|]. split.
    * exact H10'.
    * rewrite (fmw_pres _ _ 19%bv HP4 ltac:(cs_tac)), Q19, (fmw_pres _ _ 19%bv HP2 ltac:(cs_tac)), R19.
      exact H19.
Qed.

(* ---- crt_segC2: CRT_P5 (0x810a0, a0 = 1 from must_name, no compare on B): a2 := tx; snprintf (t, 3 n + 64, tx, uri)
   at 0x810b4; as_ruled (t, uri) at 0x810c0; back at CRT_P7 (fuzz_manifest.c:272-273) ---- *)
Lemma crt_segC2 : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k t,
  crt_base B cx -> crt_P5 B cx ly' S' W' regs' mem' md' k t ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 k2, crt_P7 B cx ly2 S2 W2 regs2 mem2 md2 k2 t ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_P7 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_P5 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k t HB (HT & _ & H19) K7.
pose proof (AR_laws_ok tfibsegs B) as LAWS'. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & _ & Hku0 & Hlu & _).
pose proof HT as ((HJ & _ & _ & _ & _ & Hs0 & _ & Hcu & _ & _) & Hk & Hn1 & H9 & H18 & _ & Hperm & _).
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
assert (Hu64 : 0 <= cx_u cx < 2 ^ 64) by (destruct Hcu as (_ & Hu1 & Hu2 & _); lia).
(* the stretch to snprintf: a2 := tx, a0 := s2, a1 := s1, a3 := s0 *)
pose proof (fmw_resume_nr W regs [] mem CRT_P5) as HS.
unfold crt_J in HJ.
unfold cfg_at. change (w64 CRT_P5) with (Z_to_bv 64 CRT_P5).
aj_run_to fmw_tbl_crt_ok HS HJ PC_snprintf.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
set (E1 := Ereg regs []) in HS.
crt_sb0 mem (ms_mem ms1) SB1.
pose proof (fmw_reg_lit _ E1 _ ms1 1%bv CRT_P6 HS ltac:(vm_compute; reflexivity) ltac:(unfold CRT_P6; lia)) as R1.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs _ _ ms1 11%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as R11.
pose proof (fmw_reg_lit _ E1 _ ms1 12%bv FMT_tx HS ltac:(vm_compute; reflexivity) ltac:(unfold FMT_tx; lia)) as R12.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 13) 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R13.
pose proof (fmw_reg_atom _ regs _ _ ms1 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as R19.
assert (HT1 : crt_tcore B cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k t 2).
{ apply (crt_tcore_nr cx ly S W regs mem md k t 2 (ms_regs ms1) (ms_mem ms1) md1 HB HT HJ SB1); crt_keep HS. }
pose proof HT1 as ((HJ1 & _ & _ & _ & _ & _ & _ & Hcu1 & _ & _) & _).
pose proof HJ1 as (HAR1 & _).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HS eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_snprintf) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs PC_snprintf (ms_regs ms1) (ms_mem ms1) md1).
apply (crt_snp cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k t 2 CRT_P6 ps_tx FMT_tx
  (ManifestModel.txt_wholex (cx_ub cx)) _ HB HT1 R1).
- unfold CRT_P6; lia.
- reflexivity.
- rewrite R10. exact H18.
- rewrite R11. exact H9.
- rewrite R12. reflexivity.
- exact in_ps_tx.
- cbn [map]. rewrite R13, Hs0. unfold w64. rewrite (unsigned_lit_small (cx_u cx) Hu64).
  unfold ps_tx.
  apply (frender_ls W (ms_mem ms1) t _ [60] (88 :: 62 :: ManifestModel.tail_lv2) (cx_u cx) (cx_ub cx)).
  + exact Hcu1.
  + exact (crt_uri_disj cx ly S W (ms_mem ms1) md1 t (crt_tsz (cx_n cx)) (cx_u cx) (cx_ub cx) HAR1 Hperm Hku0 Hnpos).
  + reflexivity.
- rewrite txt_len_wholex. unfold crt_tsz, cx_n. lia.
- apply nz_txt_wholex. exact (proj2 (proj1 Hcu)).
- intros regs2 mem2 md2 HT2 HP2 Hout2 _.
  pose proof HT2 as ((HJ2 & _ & _ & _ & _ & Hs02 & _ & _ & _ & _) & _ & _ & _ & H182 & _).
  (* the stretch to as_ruled: a0 := s2, a1 := s0 *)
  pose proof (fmw_resume_nr W regs2 [] mem2 CRT_P6) as HS2.
  unfold crt_J in HJ2.
  unfold cfg_at. change (w64 CRT_P6) with (Z_to_bv 64 CRT_P6).
  aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_as_ruled.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3 := mdx) in * end.
  set (E3 := Ereg regs2 []) in HS2.
  crt_sb0 mem2 (ms_mem ms3) SB3.
  pose proof (fmw_reg_lit _ E3 _ ms3 1%bv CRT_P7 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_P7; lia)) as Q1.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 10%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  assert (HT3 : crt_tcore B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k t 2).
  { apply (crt_tcore_nr cx ly S W regs2 mem2 md2 k t 2 (ms_regs ms3) (ms_mem ms3) md3 HB HT2 HJ2 SB3);
      crt_keep HS2. }
  assert (Hout3 : cstr_ok tfibsegs W (ms_mem ms3) t (ManifestModel.txt_wholex (cx_ub cx))).
  { apply (cstr_ok_below W mem2 (ms_mem ms3)); [apply (same_below_mono _ _ _ _ SB3); lia | exact Hout2]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_as_ruled) (ms_mem ms3) (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs A_as_ruled (ms_regs ms3) (ms_mem ms3) md3).
  apply (crt_asr_call cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k t 2 CRT_P7
    (ManifestModel.txt_wholex (cx_ub cx)) _ HB HT3 Q1).
  + unfold CRT_P7; lia.
  + reflexivity.
  + cbv [CTX_as_ruled CRT_P7]. repeat (first [left; reflexivity | right]).
  + rewrite Q10. exact H182.
  + rewrite Q11. exact Hs02.
  + exact Hout3.
  + rewrite txt_len_wholex. unfold crt_tsz, cx_n. lia.
  + lia.
  + unfold EV_as_ruled, EV_names. lia.
  + intros ly4 S4 W4 regs4 mem4 md4 HT4 HP4 _.
    apply (K7 ly4 S4 W4 regs4 mem4 md4 (k + EV_as_ruled)).
    split; [exact HT4|].
    rewrite (fmw_pres _ _ 19%bv HP4 ltac:(cs_tac)), Q19, (fmw_pres _ _ 19%bv HP2 ltac:(cs_tac)), R19.
    exact H19.
Qed.
End C.
