(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Piece E of segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81c34 .. 0x81e18):
   the expected display string exp_dp, from the expected name exp_nm and the two widths
   (j_E_stmt of LLVMFuzzerTestOneInput_Jcut.v).
     0x81c34 .. 0x81c44  exp_nm[0] (never 0: the plain model's name always has a byte), ld = 0, the copy's cursors
     0x81c48 .. 0x81ca0  the exp_nm -> exp_dp copy loop (j_dp_loop of _Jdp.v), then ld = ln
     0x81ca4 .. 0x81ce4  " (" appended, ld = ln + 2
     0x81cfc             put_dec(exp_dp, &ld, in, 1): the decimal of `in` appended (HPD)
     0x81d00 .. 0x81d50  " in / " appended, byte by byte from image object 9 (six iterations, index 0 .. 5)
     0x81d88             put_dec(exp_dp, &ld, out, 1): the decimal of `out` appended (HPD)
     0x81d8c .. 0x81de0  " out)" appended, byte by byte from image object 10 (five iterations, index 0 .. 4)
     0x81e00 .. 0x81e14  exp_dp[ld] = 0
   The bytes are exactly SlotModel.n_EXP_DP: the name, " (", DEC(in,1), " in / ", DEC(out,1), " out)".
   Every shadow test of a destination byte is covered by the zero shadow of exp_dp the segment entered with
   (Pj3), every shadow test of a source byte of object 9 / 10 by the registered globals' shadow (GM with
   G_IN / G_OUT: a 7- and a 6-byte block, whose last granule admits index 0 .. 6 and 0 .. 5). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require LLVMFuzzerTestOneInput_Jdp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow-cell arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model: the display string, byte by byte ----------------------------------------------------- *)
Module JEModel.
Import RcIdentModel SlotModel IdentSpec.
Definition nz (b : byte) : bool := negb (bz b =? 0).
Lemma fb_nth : forall (l : list byte) j, forallb nz l = true -> (j < length l)%nat -> bz (nthb l j) <> 0.
Proof.
induction l as [|b l IH]; intros j Hf Hj; [cbn in Hj; lia|].
cbn [forallb] in Hf. apply andb_true_iff in Hf as [Hb Hf]. unfold nz in Hb.
apply negb_true_iff, Z.eqb_neq in Hb.
destruct j as [|j]; [exact Hb | exact (IH j Hf ltac:(cbn in Hj; lia))].
Qed.
Lemma fz_nz : forall l j, (j < first_zero l)%nat -> bz (nthb l j) <> 0.
Proof.
induction l as [|b l IH]; intros j Hj; [cbn in Hj; lia|].
cbn [first_zero] in Hj. destruct (Z.eqb_spec (bz b) 0) as [Hb|Hb]; [lia|].
destruct j as [|j]; [exact Hb | exact (IH j ltac:(lia))].
Qed.
Lemma nth_firstn : forall (l : list byte) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
induction l as [|b l IH]; intros k j d Hj; [rewrite firstn_nil; destruct j; reflexivity|].
destruct k as [|k]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma name_str_fb : forall idb, forallb nz (name_str idb) = true.
Proof.
intros idb. apply forallb_forall. intros b Hb. unfold nz. apply negb_true_iff, Z.eqb_neq.
unfold name_str in Hb. destruct (In_nth _ _ (zb 0) Hb) as (j & Hj & <-).
rewrite length_firstn in Hj. rewrite nth_firstn by lia. apply fz_nz. lia.
Qed.
Lemma stem_img_fb : forall f, forallb nz (stem_img f) = true.
Proof.
intros f. unfold stem_img.
destruct (f =? 1); [vm_compute; reflexivity|].
destruct (f =? 2); [vm_compute; reflexivity|].
destruct (f =? 3); vm_compute; reflexivity.
Qed.
Lemma stem_fb : forall inp, forallb nz (n_stem inp) = true.
Proof. intros inp. unfold n_stem. destruct (n_use_said inp); [apply name_str_fb | apply stem_img_fb]. Qed.
Lemma okw_range : forall v, 0 <= v < 256 -> okw v = true -> 0 <= v <= 40.
Proof.
intros v Hv H. unfold okw in H. apply orb_true_iff in H as [H|H].
- apply Z.eqb_eq in H. lia.
- apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H]. apply Z.leb_le in H. lia.
Qed.
Lemma in_range : forall inp, n_wok inp = true -> 0 <= t_in inp <= 40 /\ 0 <= t_out inp <= 40.
Proof.
intros inp H. unfold n_wok in H. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2].
split; [apply okw_range; [apply JModel.tin_range | exact H1]
       | apply okw_range; [apply JModel.tout_range | exact H2]].
Qed.
Lemma DEC_fb : forall x m, 0 <= x <= 40 -> (m = 1 \/ m = 2) -> forallb nz (DEC x m) = true.
Proof.
intros x m Hx Hm. pose proof (JModel.DEC_digits x m Hx Hm) as H.
apply forallb_forall. intros b Hb. unfold nz. apply negb_true_iff, Z.eqb_neq.
apply JModel.digit_nz. revert b Hb. apply forallb_forall. exact H.
Qed.
Lemma W4_fb : forall inp, n_wok inp = true -> forallb nz (n_W4 inp) = true.
Proof.
intros inp H. destruct (in_range inp H) as [Hi Ho].
unfold n_W4. rewrite forallb_app. apply andb_true_iff.
split; apply DEC_fb; solve [exact Hi | exact Ho | right; reflexivity].
Qed.
Lemma nm_fb : forall inp, n_wok inp = true -> forallb nz (n_EXP_NM inp) = true.
Proof.
intros inp H. unfold n_EXP_NM. destruct (n_ends_w4 inp); [apply stem_fb|].
rewrite !forallb_app, stem_fb, (W4_fb inp H). vm_compute. reflexivity.
Qed.
Lemma nm_nz : forall inp j, n_wok inp = true -> (j < length (n_EXP_NM inp))%nat ->
  bz (nthb (n_EXP_NM inp) j) <> 0.
Proof. intros inp j H Hj. exact (fb_nth _ j (nm_fb inp H) Hj). Qed.
Lemma nm_pos : forall inp, (0 < length (n_EXP_NM inp))%nat.
Proof.
intros inp. unfold n_EXP_NM. destruct (n_ends_w4 inp) eqn:E.
- unfold n_ends_w4 in E. apply andb_true_iff in E as [E1 _]. apply Nat.leb_le in E1. lia.
- rewrite !length_app. cbn [length]. lia.
Qed.
Lemma dp_eq : forall inp, n_EXP_DP inp =
  n_EXP_NM inp ++ str_bytes " ("%string ++ DEC (t_in inp) 1 ++ str_bytes " in / "%string ++
  DEC (t_out inp) 1 ++ str_bytes " out)"%string.
Proof. intros inp. reflexivity. Qed.
Lemma s1_bytes : map (fun b : byte => bv_unsigned b) (str_bytes " ("%string) = [32; 40].
Proof. vm_compute. reflexivity. Qed.
Lemma s2_bytes : map (fun b : byte => bv_unsigned b) (str_bytes " in / "%string) = [32; 105; 110; 32; 47; 32].
Proof. vm_compute. reflexivity. Qed.
Lemma s3_bytes : map (fun b : byte => bv_unsigned b) (str_bytes " out)"%string) = [32; 111; 117; 116; 41].
Proof. vm_compute. reflexivity. Qed.
Lemma s1_len : length (str_bytes " ("%string) = 2%nat.
Proof. reflexivity. Qed.
Lemma s2_len : length (str_bytes " in / "%string) = 6%nat.
Proof. reflexivity. Qed.
Lemma s3_len : length (str_bytes " out)"%string) = 5%nat.
Proof. reflexivity. Qed.
Lemma dec_len1 : forall v, 0 <= v <= 40 -> 1 <= put_dec_c.dec_len v 1 <= 2.
Proof.
intros v Hv.
assert (H : z_all (fun x => (1 <=? put_dec_c.dec_len x 1) && (put_dec_c.dec_len x 1 <=? 2)) 41 0 = true)
  by (vm_compute; reflexivity).
pose proof (z_all_spec _ 41 0 H v ltac:(lia)) as Hq. cbn beta in Hq.
apply andb_true_iff in Hq as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma dp_len : forall inp, Z.of_nat (length (n_EXP_DP inp)) =
  Z.of_nat (length (n_EXP_NM inp)) + 2 + put_dec_c.dec_len (t_in inp) 1 + 6 +
  put_dec_c.dec_len (t_out inp) 1 + 5.
Proof.
intros inp. unfold n_EXP_DP, put_dec_c.dec_len. rewrite !length_app.
rewrite s1_len, s2_len, s3_len. lia.
Qed.
(* The byte garr8 of a NUL-terminated string gives at index i <= |s| (lib/A/Prog/_Jdp.v jd_nth_src). *)
Lemma nthb_app : forall (s : list byte) j, (j <= length s)%nat -> nthb (s ++ [zb 0]) j = nthb s j.
Proof.
intros s j Hj. unfold nthb. destruct (Nat.lt_ge_cases j (length s)) as [Hl | Hg].
- rewrite app_nth1 by exact Hl. reflexivity.
- assert (j = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
  cbn [nth]. rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma nth_src : forall (s : list byte) i, (i <= length s)%nat ->
  nth i (map (fun b : byte => bv_unsigned b) (s ++ [zb 0])) 0 = bz (nthb s i).
Proof.
intros s i Hi. rewrite <- (nthb_app s i Hi). clear Hi. unfold nthb, bz.
generalize (s ++ [zb 0]). intros l. revert l.
induction i as [|i IH]; intros [|x l]; cbn; try (vm_compute; reflexivity). apply IH.
Qed.
Lemma map_nth_bz : forall (l : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bz (nthb l j).
Proof.
unfold nthb, bz. induction l as [|b l IH]; intros [|j]; cbn;
  try (vm_compute; reflexivity); apply IH.
Qed.
Lemma bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma nz_of_fb : forall l j, forallb nz l = true -> (j < length l)%nat -> nz (nthb l j) = true.
Proof. intros l j Hf Hj. unfold nz. apply negb_true_iff, Z.eqb_neq. exact (fb_nth l j Hf Hj). Qed.
End JEModel.

(* The windows of a run that writes nothing. *)
Ltac je_awr_ro :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]); apply awr_ok_nil.
(* A run whose windows are all empty writes nothing. *)
Ltac je_win_none :=
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wl wh aa Hin Hr;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; exfalso; cbn [base_val] in Hr; clear - Hr; lia | ]);
  destruct Hin.
(* A register of the symbolic state, kept as the symbolic value's denotation (lib/A/Prog/_Jdp.v jd_reg). *)
Ltac je_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* A membership in a concrete list. *)
Ltac je_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The i-th region of a symbolic state, as region_ok of the memory (lib/A/Prog/_J.v jget_region). *)
Ltac je_get_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?rg =>
      pose proof (st_ok_region_nth E (abs_ss val ss) ms i rg HS ltac:(vm_compute; reflexivity)) as HR end
  | st_ok ?segs ?E ?ss ?ms =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?rg =>
      pose proof (st_ok_region_nth E ss ms i rg HS ltac:(vm_compute; reflexivity)) as HR end
  end.
(* Every window of a run lies in one of the ranges P names (the windows' bases given by Us). *)
Ltac je_win2 U1 U2 :=
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wl wh aa Hin Hr;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; cbn [base_val] in Hr; rewrite ?U1, ?U2 in Hr;
            cbn beta; clear - Hr; lia | ]);
  destruct Hin.
(* Every window of a run that writes only the counter slot lies in [mf + 200, mf + 208). *)
Ltac je_win_cnt Ub :=
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wl wh aa Hin Hr;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; cbn [base_val] in Hr; rewrite ?Ub in Hr;
            cbn beta; clear - Hr; lia | ]);
  destruct Hin.

(* ---- the symbolic states the pieces start from ------------------------------------------------------------- *)
(* 0x81c34: exp_nm[0] (atom 32, never 0) at s10, and the counter ld = 0 at s1 + 200. *)
Definition jeA_nm : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition jeA_mf : YP09.region := YP09.mkRegion (Some 9%nat) 200 208 208 208 [YP09.mkChunk 200 (CVal 8 (SLit 0))].
Definition ss_jeA : sstate := mkSS 0x1528 sr_atoms [jeA_nm; jeA_mf] None (mkFacts [(32%nat, mkAF 1 255 0)] [] []).
(* 0x81ca0: the counter slot, written with the length the copy loop reached. *)
Definition jeA2_mf : YP09.region := YP09.mkRegion (Some 9%nat) 200 208 200 208 [].
Definition ss_jeA2 : sstate := mkSS 0x1594 sr_atoms [jeA2_mf] None (mkFacts [] [] []).
(* The shadow base the segment's checked part reads (a7), and the band its cells lie in. *)
Definition SB_E : Z := 0x7fff8000.
Definition Bx_E : sv := SOff 17 0.
Definition Bspan_E : Z * Z := (SB_E, SB_E + 2 ^ 44 - 1).
(* 0x81ca4: ld (atom 32) and `in` (atom 33) in the machine frame, exp_dp + ld (atom 34, the alias of s8 + a2)
   with the two bytes of " (" to come. *)
Definition jeB_mf : YP09.region := YP09.mkRegion (Some 9%nat) 160 208 200 208
  [YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition jeB_dp : YP09.region := YP09.mkRegion (Some 34%nat) 0 2 0 2 [].
Definition jeB_facts : facts :=
  mkFacts [(17%nat, mkAF SB_E SB_E 0); (32%nat, mkAF 1 21 0); (33%nat, mkAF 0 40 0);
           (34%nat, mkAF 4096 (2 ^ 47 - 64) 0); (24%nat, mkAF 4096 (2 ^ 47 - 64) 0);
           (9%nat, mkAF 0x7fff7f804000 (2 ^ 47) 0)] []
    [(SAlu ALU_ADD (SOff 24 0) (SOff 32 0), SOff 34 0)].
Definition ss_jeB : sstate := mkSS 0x1598 sr_atoms [jeB_dp; jeB_mf] None jeB_facts.
Definition SH_jeB : list shent := [mkSHE 34 0 2].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).

(* ---- generic facts about the symbolic values and the byte view ------------------------------------------- *)
Lemma je_w64 : forall z, w64 z = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma je_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
intros E n v c H. rewrite U_SOff, H, je_w64, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma je_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma je_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
intros E e v H. apply bv_eq. unfold U in H. rewrite H, je_w64, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma je_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. rewrite je_w64. apply unsigned_lit_small. exact Hv. Qed.
(* A byte the view shows is a byte the memory holds. *)
Lemma je_vm1 : forall H (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hz j Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
destruct (aview_byte SEGS H mem a v Hz) as (b & Hb & Hbv & Hr).
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hbv.
unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. clear - Hr. lia.
Qed.
(* Two bytes the memory holds, as garr8. *)
Lemma je_garr2 : forall (m : word -> option byte) a v0 v1,
  val_mem SEGS m (a + 0) 1 v0 -> val_mem SEGS m (a + 1) 1 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  garr8 SEGS m a [v0; v1].
Proof.
intros m a v0 v1 H0 H1 R0 R1 j Hj. cbn [length] in Hj.
destruct j as [|[|j]]; cbn [nth Z.of_nat].
- split; [exact H0 | exact R0].
- split; [exact H1 | exact R1].
- lia.
Qed.
(* A run's windows, as the shape kept_of_frame asks for. *)
Lemma je_kept_of : forall (W : world SEGS) E rs (m m2 : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) ->
     base_val E b + wlo <= a < base_val E b + whi -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a.
Proof. intros W E rs m m2 P HFr Hw. exact (kept_of_frame E rs (w_H W) m m2 P HFr Hw). Qed.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what the segment takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) ----------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
(* The contract's own event bound (LLVMFuzzerTestOneInput.v:124): put_dec asks `st_nev Sc <= EV_MAX`, which
   the entry's pre-condition gives only through it. *)
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the shared layer of segment J (LLVMFuzzerTestOneInput_Jcut.v), at this Section's variables ------------ *)
#[local] Notation jcut := (LLVMFuzzerTestOneInput_Jcut.jcut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jc := (LLVMFuzzerTestOneInput_Jcut.jc B).
#[local] Notation jcut_mk := (LLVMFuzzerTestOneInput_Jcut.jcut_mk B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation jlay_of := (LLVMFuzzerTestOneInput_Jcut.jlay_of B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK
  EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).
#[local] Notation jcut_close4 := (LLVMFuzzerTestOneInput_Jcut.jcut_close4 B MT XM_LIB XN_LIB RLO RHI RA_LLVMF
  A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0 AJ_NIL_IO).
#[local] Notation jcut_mk4 := (LLVMFuzzerTestOneInput_Jcut.jcut_mk4 B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation jcut_wr := (LLVMFuzzerTestOneInput_Jcut.jcut_wr B).
#[local] Notation jcls := (LLVMFuzzerTestOneInput_Jcut.jcls B).
#[local] Notation jkeep4 := (LLVMFuzzerTestOneInput_Jcut.jkeep4 B).

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- what a piece of the segment hands to the next ---------------------------------------------------------- *)
(* The journal at the state the piece reached, what it kept outside WJ, and the registers ecommon, jc and Pj4
   read (sp, gp, tp, s0, s1, s3 and the callee-saved s4 .. s11 the segment does not write). *)
Definition JE_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Definition jeK (g : ectx) (pos mf : Z)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  : Prop :=
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) /\
  frames S3 = [(4, pos)] /\ Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\
  jkeep4 g pos mf ly2 S2 W2 mem2 W3 mem3 /\
  (forall r : bv 5, In r JE_KEPT -> getr regs3 r = getr regs2 r) /\
  (forall fd, fd_lookup (m_fds md3) fd = fd_lookup (m_fds md2) fd) /\ m_fs md3 = m_fs md2.

Lemma jeK_refl : forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] ->
  jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs2 mem2 md2.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HJ Hfr.
split; [exact HJ|]. split; [exact Hfr|]. split; [apply Permutation_refl|].
split; [intros a _ _ _; reflexivity|]. split; [intros r _; reflexivity|].
split; [intros fd; reflexivity | reflexivity].
Qed.

(* jcls speaks of the live blocks, which a piece only permutes. *)
Lemma je_jcls_perm : forall g pos mf ly2 S2 ly3 S3 a,
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  jcls g pos mf ly2 S2 a -> jcls g pos mf ly3 S3 a.
Proof.
intros g pos mf ly2 S2 ly3 S3 a Hp [H|[(b & m & Hin & Hr)|H]]; [left; exact H| |right; right; exact H].
right; left. exists b, m. split; [exact (Permutation_in _ (Permutation_sym Hp) Hin) | exact Hr].
Qed.

Lemma jeK_trans : forall g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4,
  jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 ->
  jeK g pos mf ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 ->
  jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  (_ & _ & P1 & K1 & R1 & D1 & F1) (HJ & Hfr & P2 & K2 & R2 & D2 & F2).
split; [exact HJ|]. split; [exact Hfr|]. split; [eapply Permutation_trans; [exact P2 | exact P1]|].
split; [intros a Ha Hw Hc; rewrite (K2 a Ha Hw (je_jcls_perm g pos mf ly2 S2 ly3 S3 a P1 Hc));
        exact (K1 a Ha Hw Hc)|].
split; [intros r Hr; rewrite (R2 r Hr); exact (R1 r Hr)|].
split; [intros fd; rewrite (D2 fd); exact (D1 fd) | rewrite F2; exact F1].
Qed.

(* A call keeps every register of JE_KEPT (lib/A/Prog/_JF.v jf_pres_keep). *)
Lemma je_pres_keep : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r JE_KEPT -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. pose proof (HP (bv_unsigned r)) as E. rewrite !Z_to_bv_bv_unsigned in E. apply E.
unfold JE_KEPT in Hr. cbn [In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- context [bv_unsigned ?x] =>
     let w := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with w end; lia |]).
destruct Hr.
Qed.

(* The bytes of the two buffers the piece carries: exp_nm as it came in, and the prefix P of exp_dp built so
   far, with |P| in the counter slot mf + 200. *)
Definition jeM (g : ectx) (pos mf : Z) (P : list byte) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  sh_zero W3 mem3 (SFa g pos + V_nm) N_nm /\ sh_zero W3 mem3 (SFa g pos + V_dp) N_dp /\
  bytes_at8 W3 mem3 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]) /\
  bytes_at8 W3 mem3 (SFa g pos + V_dp) P /\
  val_mem SEGS (rd W3 mem3) (mf + M_n2) 8 (Z.of_nat (length P)).

(* The geometry of the two buffers in the entry's side-stack frame, from jlay. *)
Definition jeG (g : ectx) (pos mf : Z) : Prop :=
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\
  SFa g pos mod 64 = 0 /\ alloc_ceiling + ASTACK <= mf /\ e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\
  mf mod 32 = 0 /\ e_sp0 g <= 2 ^ 47.

Lemma jeG_of : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2,
  jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  jeG g pos mf.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 HJC Hmfb Hmf32.
pose proof (proj1 HJC) as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & _).
destruct Hmfb as [Hm1 Hm2].
unfold jeG.
exact (conj HSF0 (conj HSF1 (conj HSFapp (conj HSF64 (conj Hmf0 (conj (conj Hm1 Hm2) (conj Hmf32 Hsp47))))))).
Qed.

(* Every byte of the two buffers and of the counter slot lies in WJ. *)
Lemma jeWJ_fr : forall g pos mf a, SFa g pos + 528 <= a < SFa g pos + 696 ->
  LLVMFuzzerTestOneInput_Jcut.WJ g pos mf a.
Proof. intros g pos mf a Ha. unfold LLVMFuzzerTestOneInput_Jcut.WJ. right; right; left; exact Ha. Qed.
Lemma jeWJ_cnt : forall g pos mf a, mf + 200 <= a < mf + 216 ->
  LLVMFuzzerTestOneInput_Jcut.WJ g pos mf a.
Proof. intros g pos mf a Ha. unfold LLVMFuzzerTestOneInput_Jcut.WJ. right; left; exact Ha. Qed.

(* A shadow cell of a range of application memory is never a byte of that range. *)
Lemma je_sh_out : forall q n x i, in_app q n -> 4096 <= q -> q + n <= alloc_ceiling -> 0 <= n <= 1024 ->
  q <= x -> x <= q + n -> 0 <= i < 16 -> ~ (q <= shadow_of_addr SHADOW_OFF x + i < q + n).
Proof.
intros q n x i Happ H0 H1 Hn Hx0 Hx1 Hi.
pose proof asan_consts as (C1 & _).
pose proof (Z.mul_div_le x 8 ltac:(lia)) as Hq1.
assert (Hq0 : 0 <= x / 8) by (apply Z.div_pos; lia).
unfold shadow_of_addr, SHADOW_OFF.
destruct Happ as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg in *.
- clear - HL Hq0 Hq1 Hi Hx0 Hx1 H0 H1 Hn C1. lia.
- clear - HH Hq0 Hq1 Hi Hx0 Hx1 H0 H1 Hn C1. lia.
Qed.

(* ---- 0x81c34 .. 0x81ca4: exp_nm[0], ld = 0, and the exp_nm -> exp_dp copy loop --------------------------- *)
Lemma jeA : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  Pj3 g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1528) regs2 mem2 md2)
    (fun W3 c3 => exists regs3 mem3 md3,
       c3 = cfg_at SEGS (BASE + 0x1598) regs3 mem3 md3 /\ W3 = W2 /\
       jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 /\
       jeM g pos mf (SlotModel.n_EXP_NM (e_pl g)) W2 mem3 /\
       getr regs3 17 = w64 SHADOW_OFF).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC HJC HP.
destruct HP as (Hwok & R27 & R26 & R24 & R25 & R17 & Hlen21 & HNM & Vld & ZNM & ZDP).
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & _).
pose proof (proj1 HJC) as Hlay.
destruct Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & _).
assert (HES : ASTACK = 16384) by reflexivity.
assert (HWS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
pose proof HJ as (HAR2 & Hly2 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR2 Hin4) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres. rewrite EFa in HFpres, HFSpres.
pose proof (JEModel.nm_pos (e_pl g)) as Hspos.
pose proof (fun j Hj => JEModel.nm_nz (e_pl g) j Hwok Hj) as HsNZ.
pose proof (JEModel.bz_range (nthb (SlotModel.n_EXP_NM (e_pl g)) 0)) as Hb0r.
pose proof (HsNZ 0%nat Hspos) as Hb0nz.
set (SF := SFa g pos) in *.
set (s := SlotModel.n_EXP_NM (e_pl g)) in *.
(* the two buffers, as the copy loop asks for them *)
assert (Hnm0 : 4096 <= SF + V_nm) by (unfold V_nm; clear - HSF0; lia).
assert (Hnm1 : SF + V_nm + 32 <= alloc_ceiling) by (unfold V_nm; clear - HSF1; lia).
assert (Hnm8 : (SF + V_nm) mod 8 = 0) by (unfold V_nm; clear - HSF64; lia).
assert (Hdp0 : 4096 <= SF + V_dp) by (unfold V_dp; clear - HSF0; lia).
assert (Hdp1 : SF + V_dp + 64 <= alloc_ceiling) by (unfold V_dp; clear - HSF1; lia).
assert (Hdp8 : (SF + V_dp) mod 8 = 0) by (unfold V_dp; clear - HSF64; lia).
assert (Happ_nm : in_app (SF + V_nm) 32)
  by (apply (in_app_sub SF 1024); [exact HSFapp | unfold V_nm; lia | lia | unfold V_nm; lia]).
assert (Happ_dp : in_app (SF + V_dp) 64)
  by (apply (in_app_sub SF 1024); [exact HSFapp | unfold V_dp; lia | lia | unfold V_dp; lia]).
(* the destination is writable and present: the frame's own bytes *)
assert (HWR : jcut_wr LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(4, pos)] W2 mem2 (SF + V_dp) 64).
{ intros a Ha. split.
  - right; right; right. exists 4, pos. split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
    left. unfold V_dp in Ha. clear - Ha. lia.
  - exact (proj1 (HFpres a ltac:(unfold V_dp in Ha; clear - Ha; lia))). }
(* the environment: atom 32 is exp_nm[0] *)
remember (Eimg (Ereg regs2 [w64 (bz (nthb s 0))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs2 [w64 (bz (nthb s 0))]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 (bz (nthb s 0)))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
clear HE.
assert (E26 : ew E 26 = w64 (SF + V_nm)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E9 : ew E 9 = w64 mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (U26 : bv_unsigned (ew E 26) = SF + V_nm)
  by (rewrite E26; apply je_unsigned; clear - Hnm0 Hnm1 C1; lia).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite E9; apply je_unsigned; clear - Hmf0 Hsp47 Hmfb C1 HES; lia).
(* exp_nm[0], the byte the first load reads *)
assert (Hb0 : val_mem SEGS (rd W2 mem2) (SF + V_nm + 0) 1 (bz (nthb s 0))).
{ destruct (HNM 0%nat ltac:(rewrite length_map, length_app; cbn [length]; lia)) as [Hv _].
  change (Z.of_nat 0) with 0 in Hv. rewrite (JEModel.nth_src s 0%nat ltac:(lia)) in Hv. exact Hv. }
assert (HS : st_ok_pi SEGS VAL E ss_jeA
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1528)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jeA. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold jeA_nm, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U26.
      split; [clear - Hnm0; lia|]. split; [clear - Hnm1 C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + V_nm) 0 1 (SOff 32 0) (bz (nthb s 0))).
      * apply je_sv. rewrite (je_U E 32 _ 0 E32), Z.add_0_r.
        rewrite Z.mod_small by (clear - Hb0r; lia). reflexivity.
      * change (2 ^ (8 * Z.of_N 1)) with 256. exact Hb0r.
      * cbn. lia.
      * exact Hb0.
    + unfold jeA_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1 HES; lia|]. split; [clear - Hsp47 Hmfb; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 200 8 (SLit 0) 0).
      * apply je_sv. rewrite je_Ulit. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * exact Vld.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, jeA_nm, jeA_mf.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U26, U9.
    repeat split; try exact I. left. clear - Hnm1 Hmf0 C1 HES. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32.
    rewrite je_unsigned by (clear - Hb0r; lia). rewrite Z.pow_0_r, Z.mod_1_r.
    split; [clear - Hb0nz Hb0r; lia|]. split; [reflexivity | clear - Hb0r; lia]. }
unfold cfg_at. change (w64 (BASE + 0x1528)) with (Z_to_bv 64 (BASE + 0x1528)).
pose proof HJ as HJ0.
(* 0x81c34 .. 0x81c44: exp_nm[0] is not 0, so the copy loop is entered with ld = 0 *)
paj_run_to_sh RUNTOP HS HJ 0x153c; [ je_awr_ro | ].
assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  refine (je_kept_of W2 _ _ _ _ (fun _ : Z => False) HFr _ a Ha _).
  - je_win_none.
  - cbn beta. intros Hbot. exact Hbot. }
pose proof (regs_kept_of_st_ok_pi E _ _ regs2 _ [2; 3; 4; 8; 9; 17; 19; 20; 21; 22; 24; 25; 26; 27]%bv
  HS HAE ltac:(vm_compute; reflexivity)) as RK1.
cbn [ms_regs restrict] in RK1.
je_reg HS (10%bv : bv 5) Q10. je_reg HS (13%bv : bv 5) Q13. je_reg HS (12%bv : bv 5) Q12.
je_reg HS (14%bv : bv 5) Q14.
(* the loop's premises, at the memory the first run reached *)
assert (ZNM' : zero_shadow (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (SF + V_nm) 32).
{ apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZNM].
  intros i Hi. apply KD. unfold shadow_of_addr, SHADOW_OFF.
  assert (0 <= (SF + V_nm) / 8 <= SF + V_nm)
    by (split; [apply Z.div_pos; clear - Hnm0; lia | apply Z.div_le_upper_bound; clear - Hnm0; lia]).
  change (32 / 8) with 4 in Hi. clear - Hi H Hnm1 C1. lia. }
assert (ZDP' : zero_shadow (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (SF + V_dp) 64).
{ apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZDP].
  intros i Hi. apply KD. unfold shadow_of_addr, SHADOW_OFF.
  assert (0 <= (SF + V_dp) / 8 <= SF + V_dp)
    by (split; [apply Z.div_pos; clear - Hdp0; lia | apply Z.div_le_upper_bound; clear - Hdp0; lia]).
  change (64 / 8) with 8 in Hi. clear - Hi H Hdp1 C1. lia. }
assert (HNM' : garr8 SEGS (rd W2 (ms_mem ms)) (SF + V_nm)
                 (map (fun b : byte => bv_unsigned b) (s ++ [zb 0]))).
{ apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact HNM].
  intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk.
  apply KD. clear - Hk Hnm0 Hnm1 C1 Hlen21. lia. }
assert (Vld' : val_mem SEGS (rd W2 (ms_mem ms)) (mf + M_n2) 8 0).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (mf + M_n2) (mf + M_n2) 8 0); [|exact Vld].
  intros k Hk. apply KD. unfold M_n2. cbn in Hk. clear - Hk Hmf0 Hsp47 Hmfb C1 HES. lia. }
assert (HWR' : jcut_wr LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(4, pos)] W2 (ms_mem ms)
                 (SF + V_dp) 64).
{ pose proof (proj1 HJ) as HAR3.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR3 Hin4) as (_ & _ & HFpres3 & _).
  change (fs_frame_bytes 4) with 1024 in HFpres3. rewrite EFa in HFpres3. fold SF in HFpres3.
  intros a Ha. split.
  - right; right; right. exists 4, pos. split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024. fold SF.
    left. unfold V_dp in Ha. clear - Ha. lia.
  - exact (proj1 (HFpres3 a ltac:(unfold V_dp in Ha; clear - Ha; lia))). }
(* the copy loop of _Jdp.v *)
pmkst HS.
eapply SRr_bind;
 [ apply (LLVMFuzzerTestOneInput_Jdp.j_dp_loop B LAWS LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g) (e_W g)
     (e_mem g) (e_md g) ly2 S2 W2 (4 * Z.of_nat (m_nrec g) + 7) (SF + V_nm) (SF + V_dp) 0 s 0%nat) | ].
- exact HJ.
- rewrite (RK1 3%bv ltac:(cbn; tauto)). exact Rgp.
- rewrite (RK1 4%bv ltac:(cbn; tauto)). exact Rtp.
- rewrite (RK1 17%bv ltac:(cbn; tauto)). exact R17.
- rewrite Q10. apply je_sv. rewrite (je_U E 26 _ 1 E26). f_equal; clear; unfold V_nm; lia.
- rewrite Q13. apply je_sv. rewrite (je_U E 26 _ 1 E26). f_equal; clear; unfold V_nm; lia.
- rewrite Q12. apply je_sv. rewrite je_Ulit. f_equal; clear; lia.
- rewrite Q14. apply je_sv. rewrite (je_U E 32 _ 0 E32). f_equal; clear; lia.
- rewrite (RK1 24%bv ltac:(cbn; tauto)). exact R24.
- exact Hspos.
- exact Hlen21.
- exact HsNZ.
- exact HNM'.
- lia.
- clear - Hlen21. lia.
- exact ZNM'.
- exact ZDP'.
- exact HWR'.
- intros m Hm. lia.
- exact Happ_nm.
- exact Happ_dp.
- exact Hnm0.
- exact Hnm1.
- exact Hnm8.
- exact Hdp0.
- exact Hdp1.
- exact Hdp8.
- left. clear. unfold V_nm, V_dp. lia.
- (* 0x81ca0: the loop's length goes back into the counter slot *)
  intros W3 c3 _ (-> & regsF & memF & mdF & -> & HJF & RKF & R12F & WLF & KLF & GLF).
  clear HF HFr HG HS Q10 Q13 Q12 Q14.
  pose proof HJF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _).
  assert (RKF9 : getr regsF 9 = w64 mf)
    by (rewrite (RKF 9%bv ltac:(cbn; tauto)), (RK1 9%bv ltac:(cbn; tauto)); exact Rs1).
  remember (Eimg (Ereg regsF [])) as E' eqn:HE'.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply Eimg_env).
  assert (EE' : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E' n = getr regsF r)
    by (intros n r Hn; rewrite HE'; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (ER' : regs_ok E' sr_atoms regsF) by (rewrite HE'; apply regs_ok_Eimg_Ereg).
  assert (HAE' : env_agree 32 (Ereg regsF []) E')
    by (rewrite HE'; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE'.
  assert (E'9 : ew E' 9 = w64 mf) by (rewrite (EE' 9%nat 9%bv eq_refl); exact RKF9).
  assert (E'12 : ew E' 12 = w64 (Z.of_nat (length s)))
    by (rewrite (EE' 12%nat 12%bv eq_refl), R12F; f_equal; clear; lia).
  assert (U9' : bv_unsigned (ew E' 9) = mf)
    by (rewrite E'9; apply je_unsigned; clear - Hmf0 Hsp47 Hmfb C1 HES; lia).
  assert (HS2 : st_ok_pi SEGS VAL E' ss_jeA2
    (restrict (w_H W2) (mkst regsF (Z_to_bv 64 (BASE + 0x1594)) memF (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jeA2. apply pa_entry_st_ok_full.
    - exact ER'.
    - vm_compute. reflexivity.
    - constructor; [|constructor].
      unfold jeA2_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9'.
      split; [clear - Hmf0 C1 HES; lia|]. split; [clear - Hsp47 Hmfb; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HpresF.
      clear - Ho Hmfb HWS. lia.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 (BASE + 0x1594)) with (Z_to_bv 64 (BASE + 0x1594)).
  paj_run_to_sh RUNTOP HS2 HJF 0x1598;
   [ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
       let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
     repeat first
     [ apply awr_ok_nil
     | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
     | eapply awr_ok_cons_gen;
       [ reflexivity | exact U9'
       | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; clear - Ha Hmfb HWS; lia
       | ] ]
   | ].
  cbn [ms_mem mkst] in HFr.
  pose proof (je_kept_of W2 _ _ _ _ (fun a => mf + 200 <= a < mf + 208) HFr
    ltac:(je_win_cnt U9')) as KEEP2.
  cbn beta in KEEP2.
  pose proof (regs_kept_of_st_ok_pi E' _ _ regsF _ (17%bv :: JE_KEPT) HS2 HAE'
    ltac:(vm_compute; reflexivity)) as RK2.
  cbn [ms_regs restrict] in RK2.
  je_get_region HS2 0%nat RR. cbn [ms_mem restrict] in RR.
  assert (VldN : val_mem SEGS (rd W2 (ms_mem ms0)) (mf + M_n2) 8 (Z.of_nat (length s))).
  { apply (field_of_region E' (rd W2 (ms_mem ms0)) 9%nat mf _ 200 208 200 208 200 8%N (SOff 12 0)
      (Z.of_nat (length s)) RR U9' ltac:(je_in)
      ltac:(apply je_sv; rewrite (je_U E' 12 _ 0 E'12); f_equal; clear; lia)
      ltac:(clear - Hlen21; cbn; lia) ltac:(cbn; lia)). }
  (* the counter slot is the only byte the last run changed; the loop changed only exp_dp *)
  assert (KSH : forall x i, 0 <= x -> x <= alloc_ceiling -> 0 <= i < 16 ->
            aview SEGS (w_H W2) (ms_mem ms0) (shadow_of_addr SHADOW_OFF x + i) =
            aview SEGS (w_H W2) memF (shadow_of_addr SHADOW_OFF x + i)).
  { intros x i Hx0 Hx1 Hi. unfold shadow_of_addr, SHADOW_OFF.
    pose proof (Z.mul_div_le x 8 ltac:(lia)) as Hq1.
    assert (Hq0 : 0 <= x / 8) by (apply Z.div_pos; lia).
    apply KEEP2; clear - Hi Hx0 Hx1 Hq0 Hq1 Hmf0 C1 HES; lia. }
  assert (KFR : forall x, SF <= x -> x < SF + 1024 ->
            aview SEGS (w_H W2) (ms_mem ms0) x = aview SEGS (w_H W2) memF x).
  { intros x H1 H2. apply KEEP2; clear - H1 H2 HSF0 HSF1 Hmf0 C1 HES; lia. }
  (* what the piece hands on *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ LLVMFuzzerTestOneInput_Jcut.WJ g pos mf a ->
            aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hw.
    assert (Hc1 : ~ (mf + 200 <= a < mf + 208))
      by (intros Hc; apply Hw; apply jeWJ_cnt; clear - Hc; lia).
    assert (Hc2 : ~ (SF + V_dp + 0 <= a < SF + V_dp + 0 + Z.of_nat (length s))).
    { intros Hc. apply Hw. apply jeWJ_fr. fold SF. unfold V_dp in Hc. clear - Hc Hlen21. lia. }
    rewrite (KEEP2 a Ha Hc1). rewrite (KLF a Ha Hc2). exact (KD a Ha). }
  pmkst HS2. apply SRr_ret.
  do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
  split.
  { split; [exact HJF|]. split; [exact Hfrs|]. split; [apply Permutation_refl|].
    split; [apply LLVMFuzzerTestOneInput_Jcut.jkeep4_of; exact KALL|].
    split.
    { intros r Hr. rewrite (RK2 r ltac:(cbn [In] in Hr |- *; tauto)).
      rewrite (RKF r ltac:(unfold JE_KEPT in Hr; cbn [In] in Hr |- *; tauto)).
      exact (RK1 r ltac:(unfold JE_KEPT in Hr; cbn [In] in Hr |- *; tauto)). }
    destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [D1 D2].
    destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [D3 D4].
    split; [intros fd; rewrite D3, D1; reflexivity | rewrite D4, D2; reflexivity]. }
  split.
  { assert (HSH : forall x i, SF <= x -> x <= SF + 1024 -> 0 <= i < 16 ->
             aview SEGS (w_H W2) memF (shadow_of_addr SHADOW_OFF x + i) =
             aview SEGS (w_H W2) (ms_mem ms) (shadow_of_addr SHADOW_OFF x + i)).
    { intros x i Hx0 Hx1 Hi. apply KLF.
      - unfold shadow_of_addr, SHADOW_OFF.
        pose proof (Z.mul_div_le x 8 ltac:(clear - Hx0 HSF0; lia)) as Hq1.
        assert (Hq0 : 0 <= x / 8) by (apply Z.div_pos; clear - Hx0 HSF0; lia).
        clear - Hi Hx0 Hx1 Hq0 Hq1 HSF0 HSF1 C1. lia.
      - intros Hc.
        apply (je_sh_out SF 1024 x i HSFapp HSF0 HSF1 ltac:(clear; lia) Hx0 Hx1 Hi).
        unfold V_dp in Hc. clear - Hc Hlen21. lia. }
    split.
    { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) memF)).
      - intros i Hi. apply KSH; [clear - Hnm0; lia | clear - Hnm1; lia |
          unfold N_nm in Hi; change (32 / 8) with 4 in Hi; clear - Hi; lia].
      - apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) (ms_mem ms)));
          [|exact ZNM'].
        intros i Hi. apply HSH; [unfold V_nm; clear; lia | unfold V_nm; clear; lia |
          unfold N_nm in Hi; change (32 / 8) with 4 in Hi; clear - Hi; lia]. }
    split.
    { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) memF)).
      - intros i Hi. apply KSH; [clear - Hdp0; lia | clear - Hdp1; lia |
          unfold N_dp in Hi; change (64 / 8) with 8 in Hi; clear - Hi; lia].
      - apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) (ms_mem ms)));
          [|exact ZDP'].
        intros i Hi. apply HSH; [unfold V_dp; clear; lia | unfold V_dp; clear; lia |
          unfold N_dp in Hi; change (64 / 8) with 8 in Hi; clear - Hi; lia]. }
    split.
    { apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) memF (ms_mem ms0));
        [|apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) (ms_mem ms) memF);
          [|exact HNM']].
      - intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk. fold s in Hk.
        apply KFR.
        + clear - Hk. unfold V_nm. lia.
        + clear - Hk Hlen21. unfold V_nm. lia.
      - intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk. fold s in Hk.
        apply KLF.
        + clear - Hk Hlen21 Hnm0 Hnm1 C1. lia.
        + clear - Hk Hlen21. unfold V_nm, V_dp. lia. }
    split.
    { intros j Hj. rewrite length_map in Hj.
      rewrite (JEModel.map_nth_bz s j).
      split; [|exact (JEModel.bz_range (nthb s j))].
      apply je_vm1. fold SF.
      rewrite (KFR (SF + V_dp + Z.of_nat j) ltac:(unfold V_dp; clear; lia)
                 ltac:(unfold V_dp; clear - Hj Hlen21; lia)).
      replace (SF + V_dp + Z.of_nat j) with (SF + V_dp + 0 + Z.of_nat j) by (clear; lia).
      exact (WLF j Hj). }
    exact VldN. }
  rewrite (RK2 17%bv ltac:(cbn; tauto)), (RKF 17%bv ltac:(cbn; tauto)),
          (RK1 17%bv ltac:(cbn; tauto)). exact R17.
Qed.

(* ---- the shadow facts a call asks of its two ranges ------------------------------------------------------- *)
Lemma je_mod8_4096 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof. intros x H. lia. Qed.
(* The machine stack's shadow is zero over the whole stack (AR_zshadow_law). *)
Lemma je_stack_zs : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md ->
  zero_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) /\
  ly_stk_lo ly mod 8 = 0 /\ ly_stk_hi ly mod 8 = 0.
Proof.
intros ly S W mem md HAR.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
split; [exact Hz|]. split; [apply je_mod8_4096; exact Hpal | apply je_mod8_4096; exact Hpah].
Qed.
(* A zero shadow over [lo, hi) makes the hull of any inner range, with a 64-byte margin, readable. *)
Lemma je_hull_zero : forall (rdr : reader) lo hi a n,
  lo mod 8 = 0 -> hi mod 8 = 0 -> lo + 64 <= a -> 0 < n -> a + n + 64 <= hi ->
  zero_shadow rdr SHADOW_OFF lo (hi - lo) -> shadow_hull_vis rdr a n.
Proof.
intros rdr lo hi a n Hlo Hhi Ha Hn Hah HZ s Hs.
unfold shadow_addr, shadow_of_addr in Hs.
assert (Hi : 0 <= s - (SHADOW_OFF + lo / 8) < (hi - lo) / 8) by (clear - Hlo Hhi Ha Hn Hah Hs; lia).
replace s with (shadow_of_addr SHADOW_OFF lo + (s - (SHADOW_OFF + lo / 8)))
  by (unfold shadow_of_addr; clear; lia).
rewrite (HZ _ Hi). discriminate.
Qed.
(* The side frame's own shadow cells are present, so the hull of an inner range is readable. *)
Lemma je_hull_pres : forall (W : world SEGS) mem F a n,
  F mod 64 = 0 -> F + 64 <= a -> 0 < n -> a + n + 64 <= F + 1024 ->
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr F + i)) ->
  shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros W mem F a n HF Ha Hn Hah HP s Hs.
unfold shadow_addr, shadow_of_addr in Hs.
assert (Hi : 0 <= s - (SHADOW_OFF + F / 8) < 128) by (clear - HF Ha Hn Hah Hs; lia).
replace s with (shadow_addr F + (s - (SHADOW_OFF + F / 8)))
  by (unfold shadow_addr, shadow_of_addr; clear; lia).
apply (aview_some_of_apresent SEGS). apply HP. exact Hi.
Qed.

(* ---- a put_dec(exp_dp, &ld, v, 1) call ---------------------------------------------------------------------- *)
(* The decimal of v is appended to exp_dp and ld grows by its length; the call keeps everything the cuts read
   (put_dec's tcj_kept classes 1, 2 and 4, which are exactly jcls). *)
Lemma je_call : forall g pos mf ly2 S2 W2 regs2 mem2 md2 (P : list byte) (v retk : Z)
  (Q : world SEGS -> config -> Prop),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  EPRE g -> getr regs2 2 = w64 mf -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  jeG g pos mf -> jeM g pos mf P W2 mem2 ->
  (1 <= Z.of_nat (length P)) -> (Z.of_nat (length P) + 2 <= 63) -> 0 <= v <= 40 ->
  (length (SlotModel.n_EXP_NM (e_pl g)) <= 21)%nat ->
  getr regs2 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs2 10 = w64 (SFa g pos + V_dp) -> getr regs2 11 = w64 (mf + M_n2) ->
  getr regs2 12 = w64 v -> getr regs2 13 = w64 1 ->
  (forall ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
     ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
       ly3 S3 W3 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
     frames S3 = frames S2 -> ablocks B ly3 S3 = ablocks B ly2 S2 ->
     aregs_preserved regs2 regs3 ->
     jeM g pos mf (P ++ IdentSpec.DEC v 1) W3 mem3 ->
     jkeep4 g pos mf ly2 S2 W2 mem2 W3 mem3 ->
     SRr SEGS W3 (cfg_at SEGS (BASE + retk) regs3 mem3 md3) Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + AF_put_dec) regs2 mem2 md2) Q.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 P v retk Q HJ Hfrs HK HPRE Rsp Rgp Rtp HG HM HP1 HP63 Hv Hnm21
  Rra Hrk0 Hrk2 R10 R11 R12 R13 HQ.



destruct HG as (HSF0 & HSF1 & HSFapp & HSF64 & Hmf0 & Hmfb & Hmf32 & Hsp47).
pose proof HM as (ZNM & ZDP & BNM & BDP & Vld).
pose proof asan_consts as (C1 & _).
assert (HES : ASTACK = 16384) by reflexivity. assert (HESt : ESTACK = 4096) by reflexivity.
assert (HWS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (HPDS : put_dec.PUT_DEC_STK = 4224) by reflexivity.
pose proof HJ as (HAR & Hly & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres. rewrite EFa in HFpres, HFSpres.
set (SF := SFa g pos) in *.

pose proof (JEModel.dec_len1 v Hv) as Hdl.
(* the two ranges the call touches *)
assert (Hdp0 : 4096 <= SF + V_dp) by (unfold V_dp; clear - HSF0; lia).
assert (Hp8 : (mf + M_n2) mod 8 = 0) by (unfold M_n2; clear - Hmf32; lia).
assert (HstkR : forall a, mf + M_n2 <= a < mf + M_n2 + 8 -> ly_stk_lo ly2 <= a < ly_stk_hi ly2).
{ intros a Ha. unfold M_n2 in Ha. rewrite Eslo, Eshi. clear - Ha Hmfb Hslo Hshi HWS. unfold e_sp0 in *. lia. }
assert (WRp : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(4, pos)] W2 mem2 mf (mf + M_n2) 8).
{ intros a Ha. unfold M_n2 in Ha.
  split; [left; clear - Ha Hmfb HWS; unfold e_sp0 in *; lia|].
  split; [apply Hpres; clear - Ha Hmfb HWS; unfold e_sp0 in *; lia|].
  split; [apply (al_stack _ _ LAWS ly2 S2 W2 mem2 md2 a HAR); apply HstkR; unfold M_n2; exact Ha
         | clear - Ha HESt; lia]. }
assert (WRb : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(4, pos)] W2 mem2 mf
                (SF + V_dp + Z.of_nat (length P)) (put_dec_c.dec_len v 1)).
{ intros a Ha.
  assert (Hfa : SF <= a < SF + 1024) by (unfold V_dp in Ha; clear - Ha HP1 HP63 Hdl; lia).
  split.
  - right; right; right. exists 4, pos. split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024. fold SF.
    left. clear - Hfa. lia.
  - split; [exact (proj1 (HFpres a Hfa))|].
    split; [exact (proj2 (HFpres a Hfa)) | clear - Hfa HSF1 Hmf0 C1 HES HESt; lia]. }
(* the shadow of the two ranges *)
destruct (je_stack_zs ly2 S2 W2 mem2 md2 HAR) as (HZstk & Hlo8 & Hhi8).
assert (Hd8 : (ly_stk_hi ly2 - ly_stk_lo ly2) mod 8 = 0).
{ clear - Hlo8 Hhi8.
  pose proof (Z.div_mod (ly_stk_hi ly2) 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod (ly_stk_lo ly2) 8 ltac:(lia)) as D2.
  rewrite Hlo8 in D2. rewrite Hhi8 in D1.
  replace (ly_stk_hi ly2 - ly_stk_lo ly2) with ((ly_stk_hi ly2 / 8 - ly_stk_lo ly2 / 8) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (SRCp : tsrc_ok W2 mem2 mf (mf + M_n2) 8).
{ split.
  { intros a Ha. unfold M_n2 in Ha.
    split; [apply (aview_some_of_apresent SEGS); apply Hpres;
            clear - Ha Hmfb HWS; unfold e_sp0 in *; lia | clear - Ha HESt; lia]. }
  split.
  { apply (range_addressable_sub _ _ (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2));
    [ apply zero_shadow_range; [exact Hlo8 | exact Hd8 | exact HZstk]
    | clear - Hmfb Hslo Hshi HWS Eslo; rewrite Eslo; unfold e_sp0, M_n2 in *; lia
    | clear - Hmfb Hslo Hshi HWS Eshi; rewrite Eshi; unfold e_sp0, M_n2 in *; lia ]. }
  split.
  { apply (je_hull_zero _ (ly_stk_lo ly2) (ly_stk_hi ly2));
    [ exact Hlo8 | exact Hhi8
    | rewrite Eslo; clear - Hmfb Hslo HWS; unfold e_sp0, M_n2 in *; lia
    | clear; lia
    | rewrite Eshi; clear - Hmfb Hshi; unfold e_sp0, M_n2 in *; lia
    | exact HZstk ]. }
  split; [|split]; unfold M_n2, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd;
    clear - Hmf0 Hmfb Hsp47 C1 HES; unfold e_sp0 in *; [right; split; lia | lia | lia]. }
assert (SRCb : tsrc_ok W2 mem2 mf (SF + V_dp + Z.of_nat (length P)) (put_dec_c.dec_len v 1)).
{ split.
  { intros a Ha.
    assert (Hfa : SF <= a < SF + 1024) by (unfold V_dp in Ha; clear - Ha HP1 HP63 Hdl; lia).
    split; [apply (aview_some_of_apresent SEGS); exact (proj1 (HFpres a Hfa))
           | clear - Hfa HSF1 Hmf0 C1 HES HESt; lia]. }
  split.
  { apply (range_addressable_sub _ _ (SF + V_dp) N_dp);
    [ apply zero_shadow_range;
      [ unfold V_dp; clear - HSF64; lia | unfold N_dp; clear; lia | exact ZDP ]
    | clear - HP1; lia | unfold N_dp; clear - HP63 Hdl; lia ]. }
  split.
  { apply (je_hull_pres W2 mem2 SF);
    [ exact HSF64 | unfold V_dp; clear - HP1; lia | clear - Hdl; lia
    | unfold V_dp; clear - HP63 Hdl; lia
    | intros i Hi; exact (proj1 (HFSpres i ltac:(change (1024 / 8) with 128; clear - Hi; lia))) ]. }
  destruct HSFapp as (_ & [HL | [HH _]]);
    unfold amem_range, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, V_dp in *;
    [ split; [left; clear - HL HP63 Hdl HP1; lia|] | split; [right; clear - HH HSF1 C1 HP63 Hdl HP1; lia|] ];
    (split; [clear - HSF0 HP1; lia | clear - HSF1 C1 HP63 Hdl; lia]). }
(* the event room: the entry's pre-condition, through the contract's HEV *)
assert (HNEV : st_nev S2 + put_dec.EV_PUT_DEC <= EV_MAX).
{ unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev0 & _).
  unfold put_dec.EV_PUT_DEC. clear - Hnev Hnev0 HK HEV. lia. }
eapply SRr_bind;
 [ apply (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2
     (4 * Z.of_nat (m_nrec g) + 7) regs2 (SF + V_dp) (mf + M_n2) (Z.of_nat (length P)) v 1) | ].
- exact HJ.
- rewrite Rra. apply ret_ok_codeptr_v; [clear - Hrk0; lia | exact Hrk2].
- unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok as (HB0 & HB1 & _); clear - HB0 HB1 Hrk0; lia).
  pose proof pa_base_lo. clear - H Hrk0. lia.
- exact Rgp.
- exact Rtp.
- exact R10.
- exact R11.
- rewrite R12. unfold w64. rewrite unsigned_lit_small by (clear - Hv; lia).
  clear - Hv. apply Z.mod_small. lia.
- left. rewrite R12. unfold w64. rewrite unsigned_lit_small by (clear - Hv; lia). clear - Hv. lia.
- exact R13.
- clear. lia.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  exact Hmf32.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  rewrite HPDS. clear - Hmfb HWS. unfold e_sp0 in *. lia.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  clear - Hmfb. unfold e_sp0 in *. lia.
- rewrite Hfrs. cbn [length]. clear. lia.
- exact Hp8.
- clear - Hdp0. lia.
- clear - HP1. lia.
- exact Vld.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  exact WRp.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  exact WRb.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  exact SRCp.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  exact SRCb.
- right. unfold V_dp, M_n2. clear - HSF1 Hmf0 C1 HES HP63 Hdl. lia.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  left. unfold M_n2. clear. lia.
- unfold spZ. rewrite Rsp. rewrite je_unsigned by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  right. rewrite HPDS. unfold V_dp. clear - HSF1 Hmf0 C1 HES HP63 Hdl. lia.
- exact HNEV.
- (* the call's post, as the piece's own shape *)
  intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HRP & Hfr3 & Hab3 & HTCJ & HGAR & HVAL).
  rewrite Rra.
  pose proof HTCJ as (T1 & T2 & T3 & T4 & T5 & T6).
  unfold spZ in T1. rewrite Rsp in T1.
  rewrite je_unsigned in T1 by (clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
  rewrite HPDS in T1.
  (* the frame's bytes and shadow cells, kept except the decimal it wrote *)
  assert (KFR : forall a, SF <= a < SF + 1024 -> ~ (SF + V_dp + Z.of_nat (length P) <= a < SF + V_dp + Z.of_nat (length P) + put_dec_c.dec_len v 1) ->
            aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hne. apply (T4 4 pos a Hin4);
      [ left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 4) with 1024;
        fold SF; clear - Ha; lia
      | cbv beta; intros [Hc|Hc]; [clear - Hc Ha HSF1 Hmf0 C1 HES; unfold M_n2 in Hc; lia | exact (Hne Hc)] ]. }
  assert (KSH : forall i, 0 <= i < 128 ->
            aview SEGS (w_H W3) mem3 (shadow_addr SF + i) = aview SEGS (w_H W2) mem2 (shadow_addr SF + i)).
  { intros i Hi. apply (T4 4 pos _ Hin4);
      [ right; unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 4) with 1024;
        change (1024 / 8) with 128; fold SF; clear - Hi; lia
      | cbv beta; unfold M_n2, V_dp, shadow_addr, SHADOW_OFF;
        pose proof (Z.mul_div_le SF 8 ltac:(clear - HSF0; lia)) as Hq1;
        assert (Hq0 : 0 <= SF / 8) by (apply Z.div_pos; clear - HSF0; lia);
        destruct HSFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg in *;
        [ clear - Hi HL HSF0 HSF1 Hq0 Hq1 Hmf0 C1 HES HP1 HP63 Hdl; lia
        | clear - Hi HH HSF0 HSF1 Hq0 Hq1 Hmf0 C1 HES HP1 HP63 Hdl; lia ] ]. }
  apply HQ with (ly3 := ly3) (S3 := S3).
  + unfold put_dec.EV_PUT_DEC in HJ3. rewrite Z.add_0_r in HJ3. exact HJ3.
  + rewrite Hfr3. reflexivity.
  + exact Hab3.
  + exact HRP.
  + (* exp_nm, exp_dp and the counter *)
    unfold jeM. fold SF.
    split.
    { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZNM].
      intros i Hi. unfold N_nm in Hi. change (32 / 8) with 4 in Hi.
      replace (shadow_of_addr SHADOW_OFF (SF + V_nm) + i) with (shadow_addr SF + (66 + i))
        by (unfold shadow_of_addr, shadow_addr, V_nm; clear - HSF64; lia).
      apply KSH. clear - Hi. lia. }
    split.
    { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZDP].
      intros i Hi. unfold N_dp in Hi. change (64 / 8) with 8 in Hi.
      replace (shadow_of_addr SHADOW_OFF (SF + V_dp) + i) with (shadow_addr SF + (74 + i))
        by (unfold shadow_of_addr, shadow_addr, V_dp; clear - HSF64; lia).
      apply KSH. clear - Hi. lia. }
    split.
    { apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W3) mem2 mem3); [|exact BNM].
      intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk.
      apply KFR; [unfold V_nm; clear - Hk Hnm21; lia | unfold V_nm, V_dp; clear - Hk Hnm21 HP1; lia]. }
    split.
    { unfold bytes_at8. rewrite map_app. apply garr8_app. split.
      - apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W3) mem2 mem3); [|exact BDP].
        intros k Hk. rewrite length_map in Hk.
        apply KFR; [unfold V_dp; clear - Hk HP63 Hdl; lia | unfold V_dp; clear - Hk; lia].
      - rewrite length_map. exact HGAR. }
    rewrite length_app. unfold put_dec_c.dec_len in HVAL.
    replace (Z.of_nat (length P + length (IdentSpec.DEC v 1)))
      with (Z.of_nat (length P) + Z.of_nat (length (IdentSpec.DEC v 1))) by (clear; lia).
    exact HVAL.
  + (* what the call kept, at the bytes the cuts read *)
    intros a Ha Hw [Hc|[(b & m & Hbin & Hbr)|[Hc|Hc]]].
    * apply T1.
      -- clear - Ha Hc Hmf0 C1 HES. lia.
      -- clear - Hc. lia.
      -- cbv beta. intros [Hx|Hx];
         [ apply Hw; apply jeWJ_cnt; unfold M_n2 in Hx; clear - Hx; lia
         | clear - Hx Hc HSF1 Hmf0 C1 HES HP63 Hdl HP1; unfold V_dp in Hx; lia ].
    * replace a with (b + (a - b)) by (clear; lia).
      apply (T2 b m (a - b)); [exact Hbin | clear - Hbr; lia|].
      cbv beta.
      intros [Hx|Hx].
      -- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hbin) as (_ & _ & Hbc & _).
         unfold M_n2 in Hx. clear - Hx Hbr Hbc Hmf0 C1 HES. lia.
      -- exfalso. apply Hw. apply jeWJ_fr. fold SF. unfold V_dp in Hx. clear - Hx HP63 Hdl. lia.
    * apply KFR; [exact Hc|]. intros Hx. apply Hw. apply jeWJ_fr. fold SF.
      unfold V_dp in Hx. clear - Hx HP63 Hdl. lia.
    * fold SF in Hc. replace a with (shadow_addr SF + (a - shadow_addr SF)) by (clear; lia).
      apply KSH. clear - Hc. lia.
Qed.

(* A word of the machine frame below the counter slots, kept by every piece (it is outside WJ). *)
Lemma je_vm_mf : forall g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 o (v : Z),
  jeG g pos mf -> jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 -> 0 <= o -> o + 8 <= 200 ->
  val_mem SEGS (rd W2 mem2) (mf + o) 8 v -> val_mem SEGS (rd W3 mem3) (mf + o) 8 v.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 o v HG (_ & _ & _ & K & _) Ho0 Ho1 Hv.
destruct HG as (HSF0 & HSF1 & HSFapp & HSF64 & Hmf0 & Hmfb & Hmf32 & Hsp47).
pose proof asan_consts as (C1 & _).
assert (HES : ASTACK = 16384) by reflexivity.
assert (Hq : 0 <= SFa g pos / 8 <= SFa g pos)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
eapply LLVMFuzzerTestOneInput_Jcut.jvm4; [exact K | | exact Hv].
intros k Hk. change (Z.of_nat 8) with 8 in Hk.
split; [clear - Hk Ho0 Ho1 Hmf0 Hmfb Hsp47 C1 HES; unfold e_sp0 in *; lia|].
split; [|left; clear - Hk Ho0; lia].
unfold LLVMFuzzerTestOneInput_Jcut.WJ, shadow_addr, SHADOW_OFF.
clear - Hk Ho0 Ho1 Hmf0 HSF0 HSF1 Hq C1 HES. lia.
Qed.

(* ---- the three remaining sub-runs of piece E, as frozen statements ------------------------------------------ *)
(* Each starts at a boundary pc with the journal from the entry state, the geometry jeG, the prefix of exp_dp
   built so far (jeM) and the registers and machine-frame words its code reads; each ends at the next boundary
   pc with jeK from its own start (journal, frames, live blocks, every byte outside WJ in jcls, the registers
   JE_KEPT, the files) and the longer prefix. j_E_of_pieces below chains jeA and the three into j_E_stmt. *)

(* 0x81ca4 .. 0x81d00 (BASE + 0x1598 .. BASE + 0x15f4): " (" at exp_dp + ld, ld = ld + 2, then
   put_dec(exp_dp, &ld, in, 1) at 0x81cfc (je_call); s2 = ' ' and s7 = 1 for the next loop. *)
Definition jeB_stmt : Prop :=
  forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  EPRE g -> jeG g pos mf -> SlotModel.n_wok (e_pl g) = true ->
  (length (SlotModel.n_EXP_NM (e_pl g)) <= 21)%nat ->
  jeM g pos mf (SlotModel.n_EXP_NM (e_pl g)) W2 mem2 ->
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs2 17 = w64 SHADOW_OFF -> getr regs2 24 = w64 (SFa g pos + V_dp) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1598) regs2 mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
       c3 = cfg_at SEGS (BASE + 0x15f4) regs3 mem3 md3 /\
       jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 /\
       jeM g pos mf (SlotModel.n_EXP_NM (e_pl g) ++ SlotModel.str_bytes " ("%string ++
                     IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1) W3 mem3 /\
       getr regs3 18 = w64 32 /\ getr regs3 23 = w64 1).

(* 0x81d00 .. 0x81d8c (BASE + 0x15f4 .. BASE + 0x1680): " in / " at exp_dp + ld, byte by byte from image
   object 9 (six iterations; the shadow base a6 from mf + 176), ld = ld + 6, then put_dec(exp_dp, &ld, out, 1)
   at 0x81d88 (je_call); s7 = 1 for the next loop. *)
Definition jeC_stmt : Prop :=
  forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  EPRE g -> jeG g pos mf -> SlotModel.n_wok (e_pl g) = true ->
  (length (SlotModel.n_EXP_NM (e_pl g)) <= 21)%nat ->
  jeM g pos mf (SlotModel.n_EXP_NM (e_pl g) ++ SlotModel.str_bytes " ("%string ++
                IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1) W2 mem2 ->
  val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 SHADOW_OFF ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs2 24 = w64 (SFa g pos + V_dp) ->
  getr regs2 18 = w64 32 -> getr regs2 23 = w64 1 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x15f4) regs2 mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
       c3 = cfg_at SEGS (BASE + 0x1680) regs3 mem3 md3 /\
       jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 /\
       jeM g pos mf (SlotModel.n_EXP_NM (e_pl g) ++ SlotModel.str_bytes " ("%string ++
                     IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1 ++ SlotModel.str_bytes " in / "%string ++
                     IdentSpec.DEC (SlotModel.t_out (e_pl g)) 1) W3 mem3 /\
       getr regs3 23 = w64 1).

(* 0x81d8c .. 0x81e18 (BASE + 0x1680 .. BASE + 0x170c): " out)" at exp_dp + ld, byte by byte from image
   object 10 (five iterations; the shadow base a6 from mf + 176), then exp_dp[ld] = 0; s2 = ld = n_ld. *)
Definition jeD_stmt : Prop :=
  forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  EPRE g -> jeG g pos mf -> SlotModel.n_wok (e_pl g) = true ->
  (length (SlotModel.n_EXP_NM (e_pl g)) <= 21)%nat ->
  jeM g pos mf (SlotModel.n_EXP_NM (e_pl g) ++ SlotModel.str_bytes " ("%string ++
                IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1 ++ SlotModel.str_bytes " in / "%string ++
                IdentSpec.DEC (SlotModel.t_out (e_pl g)) 1) W2 mem2 ->
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 SHADOW_OFF ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs2 24 = w64 (SFa g pos + V_dp) -> getr regs2 23 = w64 1 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1680) regs2 mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
       c3 = cfg_at SEGS (BASE + 0x170c) regs3 mem3 md3 /\
       jeK g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 /\
       sh_zero W3 mem3 (SFa g pos + V_nm) N_nm /\ sh_zero W3 mem3 (SFa g pos + V_dp) N_dp /\
       bytes_at8 W3 mem3 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]) /\
       bytes_at8 W3 mem3 (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0]) /\
       getr regs3 18 = w64 (SlotModel.n_ld (e_pl g))).

(* ---- 0x81ca4 .. 0x81d00: " (" and put_dec(exp_dp, &ld, in, 1) --------------------------------------------- *)
Lemma jeB : jeB_stmt.
Proof.
unfold jeB_stmt.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HK HPRE HG Hwok Hnm21 HM Vin
  Rsp Rs1 Rgp Rtp R17 R24.
pose proof HG as HG0.
destruct HG0 as (HSF0 & HSF1 & HSFapp & HSF64 & Hmf0 & Hmfb & Hmf32 & Hsp47).
pose proof HM as (ZNM & ZDP & BNM & BDP & Vld).
pose proof asan_consts as (C1 & _).
assert (HES : ASTACK = 16384) by reflexivity.
assert (HWS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
pose proof HJ as (HAR & Hly & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres. rewrite EFa in HFpres, HFSpres.
pose proof (JEModel.nm_pos (e_pl g)) as Hspos.
destruct (JEModel.in_range (e_pl g) Hwok) as [Hin0 Hout0].
set (SF := SFa g pos) in *.
set (s := SlotModel.n_EXP_NM (e_pl g)) in *.
set (ln := Z.of_nat (length s)) in *.
assert (Hln : 1 <= ln <= 21) by (unfold ln; clear - Hspos Hnm21; lia).
assert (Hdp0 : 4096 <= SF + V_dp) by (unfold V_dp; clear - HSF0; lia).
(* the environment: atom 32 = ld, 33 = in, 34 = exp_dp + ld *)
remember (Eimg (Ereg regs2 [w64 ln; w64 (SlotModel.t_in (e_pl g)); w64 (SF + V_dp + ln)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs2 [w64 ln; w64 (SlotModel.t_in (e_pl g)); w64 (SF + V_dp + ln)]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 ln)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 (SlotModel.t_in (e_pl g)))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = w64 (SF + V_dp + ln))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
clear HE.
assert (E9 : ew E 9 = w64 mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (E17 : ew E 17 = w64 SHADOW_OFF) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E24 : ew E 24 = w64 (SF + V_dp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite E9; apply je_unsigned; clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
assert (U34 : bv_unsigned (ew E 34) = SF + V_dp + ln)
  by (rewrite E34; apply je_unsigned; unfold V_dp; clear - HSF0 HSF1 C1 Hln; lia).
assert (U24 : bv_unsigned (ew E 24) = SF + V_dp)
  by (rewrite E24; apply je_unsigned; unfold V_dp; clear - HSF0 HSF1 C1; lia).
assert (U17 : bv_unsigned (ew E 17) = SHADOW_OFF)
  by (rewrite E17; apply je_unsigned; unfold SHADOW_OFF; clear; lia).
assert (U32 : bv_unsigned (ew E 32) = ln) by (rewrite E32; apply je_unsigned; clear - Hln; lia).
assert (U33 : bv_unsigned (ew E 33) = SlotModel.t_in (e_pl g))
  by (rewrite E33; apply je_unsigned; clear - Hin0; lia).
(* the symbolic state at 0x81ca4 *)
assert (HS : st_ok_pi SEGS VAL E ss_jeB
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1598)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jeB. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold jeB_dp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
      split; [clear - Hdp0 Hln; lia|]. split; [unfold V_dp; clear - HSF1 C1 Hln; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFpres (SF + V_dp + ln + o) ltac:(unfold V_dp; clear - Ho Hln; lia))).
    + unfold jeB_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1 HES; lia|]. split; [clear - Hsp47 Hmfb; unfold e_sp0 in *; lia|].
      split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres.
        clear - Ho Hmfb HWS. unfold e_sp0 in *. lia. }
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 33 0) (SlotModel.t_in (e_pl g))).
        -- apply je_sv. rewrite (je_U E 33 _ 0 E33), Z.add_0_r.
           rewrite Z.mod_small by (clear - Hin0; lia). reflexivity.
        -- cbn. clear - Hin0. lia.
        -- cbn. lia.
        -- exact Vin.
      * apply (chunk_ok_val SEGS E _ mf 200 8 (SOff 32 0) ln).
        -- apply je_sv. rewrite (je_U E 32 _ 0 E32), Z.add_0_r.
           rewrite Z.mod_small by (clear - Hln; lia). reflexivity.
        -- cbn. clear - Hln. lia.
        -- cbn. lia.
        -- unfold M_n2 in Vld. exact Vld.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, jeB_dp, jeB_mf.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U34, U9.
    repeat split; try exact I. left. unfold V_dp. clear - HSF1 Hmf0 C1 HES Hln. lia.
  - unfold facts_ok, jeB_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U17, U32, U33, U34, U24, U9, !Z.pow_0_r, !Z.mod_1_r.
      unfold SB_E, SHADOW_OFF, V_dp.
      repeat split; try reflexivity; clear - Hln Hin0 HSF0 HSF1 C1 Hmf0 Hmfb Hsp47 HES; unfold e_sp0 in *; lia.
    + split; [|exact I].
      rewrite (je_sv E (SOff 34 0) (SF + V_dp + ln))
        by (rewrite (je_U E 34 _ 0 E34), Z.add_0_r; rewrite Z.mod_small;
            [reflexivity | unfold V_dp; clear - HSF0 HSF1 C1 Hln; lia]).
      apply je_sv. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (je_U E 24 _ 0 E24), (je_U E 32 _ 0 E32), !Z.add_0_r.
      unfold zcanon, M64. rewrite <- Zplus_mod. f_equal; clear; lia. }
assert (SHOK : sh_ok SEGS Bx_E SH_jeB E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, SH_jeB. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E Bx_E 34 (SF + V_dp) N_dp (SF + V_dp + ln) 0 2).
  - apply (range_addressable_sub _ _ (SF + V_dp) N_dp);
    [ apply zero_shadow_range; [unfold V_dp; clear - HSF64; lia | unfold N_dp; clear; lia | exact ZDP]
    | clear; lia | clear; lia ].
  - unfold Bx_E. rewrite (je_U E 17 _ 0 E17), Z.add_0_r.
    rewrite Z.mod_small; [reflexivity | unfold SHADOW_OFF; clear; lia].
  - rewrite (je_U E 34 _ 0 E34), Z.add_0_r.
    apply Z.mod_small. unfold V_dp. clear - HSF0 HSF1 C1 Hln. lia.
  - clear - Hln. lia.
  - unfold N_dp. clear - Hln. lia.
  - intros x Hx Hb.
    destruct HSFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, V_dp in *.
    + clear - Hx Hb HL Hln. lia.
    + clear - Hx Hb HH Hln. lia. }
pose proof HJ as HJ0.
unfold cfg_at. change (w64 (BASE + 0x1598)) with (Z_to_bv 64 (BASE + 0x1598)).
paj_run_tok RUN HS HJ SHOK Bspan_E;
 [ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
     let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
   repeat first
   [ apply awr_ok_nil
   | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
   | eapply awr_ok_cons_gen;
     [ reflexivity | first [exact U34 | exact U9]
     | cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa;
       first [ left; clear - Haa Hmfb HWS; unfold e_sp0 in *; lia
             | right; right; right; exists 4, pos; split; [left; reflexivity|];
               unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 4) with 1024; fold SF;
               left; clear - Haa Hln HSF0; unfold V_dp in *; lia ]
     | ] ]
 | ].
(* what the run wrote: the two bytes of " (" and ld + 2 *)
pose proof (je_kept_of W2 _ _ _ _
  (fun a => SF + V_dp + ln <= a < SF + V_dp + ln + 2 \/ mf + 200 <= a < mf + 208) HFr
  ltac:(je_win2 U34 U9)) as KEEPB.
cbn beta in KEEPB.
je_get_region HS 0%nat RDP. cbn [ms_mem restrict] in RDP.
je_get_region HS 1%nat RMF. cbn [ms_mem restrict] in RMF.
assert (B0 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ln + 0) 1 32)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ln) _ 0 2 0 2 0 1%N (SLit 32) 32 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (B1 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ln + 1) 1 40)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ln) _ 0 2 0 2 1 1%N (SLit 40) 40 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (VldB : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 200) 8 (ln + 2)).
{ lazymatch type of RMF with region_ok _ ?Ef _ _ =>
    assert (E32f : ew Ef 32 = w64 ln) by (repeat rewrite ew_ewset_other by lia; exact E32);
    exact (field_of_region Ef _ 9%nat mf _ 160 208 200 208 200 8%N (SOff 32 2) (ln + 2) RMF
             ltac:(repeat rewrite ew_ewset_other by lia; exact U9) ltac:(je_in)
             ltac:(apply je_sv; rewrite (je_U Ef 32 _ 2 E32f); reflexivity) ltac:(clear - Hln; cbn; lia)
             ltac:(cbn; lia)) end. }
(* the call put_dec(exp_dp, &ld, in, 1) at 0x81cfc *)
lazymatch type of HS with st_ok _ ?Ef _ _ =>
  assert (HAEf : env_agree 32 (Ereg regs2 [w64 ln; w64 (SlotModel.t_in (e_pl g)); w64 (SF + V_dp + ln)]) Ef)
    by (destruct HAE as [HA1 HA2]; split;
        [intros n Hn; repeat rewrite ew_ewset_other by lia; exact (HA1 n Hn) | exact HA2]);
  pose proof (regs_kept_of_st_ok SEGS Ef _ _ regs2 _ JE_KEPT HS HAEf
    ltac:(vm_compute; reflexivity)) as RKB;
  assert (E24f : ew Ef 24 = w64 (SF + V_dp)) by (repeat rewrite ew_ewset_other by lia; exact E24);
  assert (E33f : ew Ef 33 = w64 (SlotModel.t_in (e_pl g))) by (repeat rewrite ew_ewset_other by lia; exact E33);
  assert (U9f : bv_unsigned (ew Ef 9) = mf) by (repeat rewrite ew_ewset_other by lia; exact U9);
  assert (E9f : ew Ef 9 = w64 mf) by (repeat rewrite ew_ewset_other by lia; exact E9) end.
cbn [ms_regs restrict] in RKB.
pmkst HS.
rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
prreg HS (1%bv : bv 5) Rra.
je_reg HS (10%bv : bv 5) Ra0. je_reg HS (11%bv : bv 5) Ra1. je_reg HS (12%bv : bv 5) Ra2.
je_reg HS (13%bv : bv 5) Ra3. je_reg HS (18%bv : bv 5) Rs2. je_reg HS (23%bv : bv 5) Rs7.
lazymatch type of HS with st_ok _ ?Ef _ _ =>
  assert (Rs2' : getr (ms_regs ms) 18 = w64 32)
    by (rewrite Rs2; apply je_sv; rewrite (je_Ulit Ef); reflexivity);
  assert (Rs7' : getr (ms_regs ms) 23 = w64 1)
    by (rewrite Rs7; apply je_sv; rewrite (je_Ulit Ef); reflexivity) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS (BASE + AF_put_dec) rg mm mdx) Q) end.
(* what the piece carries into the call *)
assert (MB : jeM g pos mf (s ++ SlotModel.str_bytes " ("%string) W2 (ms_mem ms)).
{ split.
  { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZNM].
    intros i Hi. unfold N_nm in Hi. change (32 / 8) with 4 in Hi. apply KEEPB.
    - unfold shadow_of_addr, SHADOW_OFF, V_nm.
      assert (0 <= (SF + 528) / 8 <= SF + 528)
        by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
      clear - Hi H HSF0 HSF1 C1. lia.
    - intros [Hc|Hc].
      + apply (je_sh_out SF 1024 (SF + V_nm) i HSFapp HSF0 HSF1 ltac:(clear; lia)
                 ltac:(unfold V_nm; clear; lia) ltac:(unfold V_nm; clear; lia) ltac:(clear - Hi; lia)).
        unfold shadow_of_addr, SHADOW_OFF, V_nm, V_dp in *. clear - Hc Hln. lia.
      + unfold shadow_of_addr, SHADOW_OFF, V_nm in *.
        assert (0 <= (SF + 528) / 8 <= SF + 528)
          by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
        clear - Hi H HSF0 HSF1 C1 Hmf0 HES Hc. lia. }
  split.
  { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZDP].
    intros i Hi. unfold N_dp in Hi. change (64 / 8) with 8 in Hi. apply KEEPB.
    - unfold shadow_of_addr, SHADOW_OFF, V_dp.
      assert (0 <= (SF + 592) / 8 <= SF + 592)
        by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
      clear - Hi H HSF0 HSF1 C1. lia.
    - intros [Hc|Hc].
      + apply (je_sh_out SF 1024 (SF + V_dp) i HSFapp HSF0 HSF1 ltac:(clear; lia)
                 ltac:(unfold V_dp; clear; lia) ltac:(unfold V_dp; clear; lia) ltac:(clear - Hi; lia)).
        unfold shadow_of_addr, SHADOW_OFF, V_nm, V_dp in *. clear - Hc Hln. lia.
      + unfold shadow_of_addr, SHADOW_OFF, V_dp in *.
        assert (0 <= (SF + 592) / 8 <= SF + 592)
          by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
        clear - Hi H HSF0 HSF1 C1 Hmf0 HES Hc. lia. }
  split.
  { apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact BNM].
    intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk. fold s in Hk.
    assert (Hk21 : 0 <= k <= 21) by (clear - Hk Hnm21; lia).
    apply KEEPB; [clear - Hk21 HSF0 HSF1 C1; unfold V_nm; lia
                 | clear - Hk21 Hln HSF0 HSF1 C1 Hmf0 HES; unfold V_nm, V_dp; lia]. }
  split.
  { unfold bytes_at8. rewrite map_app. apply garr8_app. split.
    - apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact BDP].
      intros k Hk. rewrite length_map in Hk. fold s in Hk. fold ln in Hk.
      apply KEEPB; [clear - Hk Hln HSF0 HSF1 C1; unfold V_dp; lia
                   | clear - Hk Hln HSF0 HSF1 C1 Hmf0 HES; unfold V_dp; lia].
    - rewrite length_map. fold s. fold ln. rewrite JEModel.s1_bytes.
      exact (je_garr2 _ (SF + V_dp + ln) 32 40 B0 B1 ltac:(clear; lia) ltac:(clear; lia)). }
  rewrite length_app. fold s. rewrite JEModel.s1_len. unfold M_n2.
  replace (Z.of_nat (length s + 2)) with (ln + 2) by (unfold ln; clear; lia). exact VldB. }
eapply (je_call g pos mf ly2 S2 W2 _ (ms_mem ms) _ (s ++ SlotModel.str_bytes " ("%string)
  (SlotModel.t_in (e_pl g)) 0x15f4).
- exact HJ.
- exact Hfrs.
- exact HK.
- exact HPRE.
- rewrite (RKB 2%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rsp.
- rewrite (RKB 3%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rgp.
- rewrite (RKB 4%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rtp.
- exact HG.
- exact MB.
- rewrite length_app. fold s. rewrite JEModel.s1_len. clear - Hln. unfold ln in *. lia.
- rewrite length_app. fold s. rewrite JEModel.s1_len. clear - Hln. unfold ln in *. lia.
- clear - Hin0. lia.
- exact Hnm21.
- exact Rra.
- clear. lia.
- clear. reflexivity.
- rewrite Ra0. apply je_sv. rewrite (je_U _ 24 _ 0 E24f). f_equal; clear; lia.
- rewrite Ra1. apply je_sv. rewrite (je_U _ 9 _ 200 E9f). unfold M_n2. f_equal; clear; lia.
- rewrite Ra2. apply je_sv. rewrite (je_U _ 33 _ 0 E33f). f_equal; clear; lia.
- rewrite Ra3. apply je_sv. rewrite je_Ulit. reflexivity.
- (* after the call *)
  intros ly3 S3 W3 regs3 mem3 md3 HJ3 Hfr3 Hab3 HRP MD HKC.
  apply SRr_ret.
  exists ly3, S3, regs3, mem3, md3.
  split; [reflexivity|].
  split.
  { split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfrs|].
    split; [rewrite Hab3; apply Permutation_refl|].
    split.
    { intros a Ha Hw Hc. rewrite (HKC a Ha Hw Hc). apply KEEPB; [exact Ha|].
      intros [Hx|Hx]; [apply Hw; apply jeWJ_fr; fold SF; unfold V_dp in Hx; clear - Hx Hln; lia
                      | apply Hw; apply jeWJ_cnt; clear - Hx; lia]. }
    split.
    { intros r Hr. rewrite (je_pres_keep _ _ HRP r Hr). exact (RKB r Hr). }
    destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [D1 D2].
    destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [D3 D4].
    split; [intros fd; rewrite D3, D1; reflexivity | rewrite D4, D2; reflexivity]. }
  split.
  { rewrite (app_assoc s (SlotModel.str_bytes " ("%string) (IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1)).
    exact MD. }
  split; [exact (eq_trans (HRP 18 ltac:(unfold acallee_saved; lia)) Rs2')
         | exact (eq_trans (HRP 23 ltac:(unfold acallee_saved; lia)) Rs7')].
Qed.

(* ---- piece E from jeA and the three sub-runs; the close is jcut_mk4 ---------------------------------------- *)
Lemma j_E_of_pieces : jeB_stmt -> jeC_stmt -> jeD_stmt ->
  LLVMFuzzerTestOneInput_Jcut.j_E_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros HB HCs HD g pos mf nm tk dp W2 c2 Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & HK & MLE & MOK & HC & HJC & HP).
pose proof HP as (Hwok & R27 & R26 & R24 & R25 & R17 & Hlen21 & _).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HJC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V160 & V168 & _).
pose proof (jeG_of g pos mf nm tk dp ly2 S2 W2 regs2 mem2 HJC Hmfb Hmf32) as HG.
(* 0x81c34 .. 0x81ca4 *)
eapply SRr_bind; [exact (jeA g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC HJC HP) |].
intros W3 c3 _ (regs3 & mem3 & md3 & -> & EW3 & K3 & M3 & R17'). subst W3.
pose proof K3 as (HJ3 & Hfr3 & _ & _ & RK3 & _).
(* 0x81ca4 .. 0x81d00 *)
eapply SRr_bind.
{ apply (HB g pos mf ly2 S2 W2 regs3 mem3 md3 HJ3 Hfr3 HK HPRE HG Hwok Hlen21 M3).
  - exact (je_vm_mf g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 160 _ HG K3
             ltac:(lia) ltac:(lia) V160).
  - rewrite (RK3 2%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rsp.
  - rewrite (RK3 9%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rs1.
  - rewrite (RK3 3%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rgp.
  - rewrite (RK3 4%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rtp.
  - exact R17'.
  - rewrite (RK3 24%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact R24. }
intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & K4 & M4 & R18 & R23).
pose proof (jeK_trans g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  K3 K4) as K24.
pose proof K24 as (HJ4 & Hfr4 & _ & _ & RK4 & _).
(* 0x81d00 .. 0x81d8c *)
eapply SRr_bind.
{ apply (HCs g pos mf ly4 S4 W4 regs4 mem4 md4 HJ4 Hfr4 HK HPRE HG Hwok Hlen21 M4).
  - exact (je_vm_mf g pos mf ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4 168 _ HG K24
             ltac:(lia) ltac:(lia) V168).
  - exact (je_vm_mf g pos mf ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4 176 _ HG K24
             ltac:(lia) ltac:(lia) V176).
  - rewrite (RK4 2%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rsp.
  - rewrite (RK4 9%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rs1.
  - rewrite (RK4 3%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rgp.
  - rewrite (RK4 4%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rtp.
  - rewrite (RK4 24%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact R24.
  - exact R18.
  - exact R23. }
intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & K5 & M5 & R23').
pose proof (jeK_trans g pos mf ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4 ly5 S5 W5 regs5 mem5 md5
  K24 K5) as K25.
pose proof K25 as (HJ5 & Hfr5 & _ & _ & RK5 & _).
(* 0x81d8c .. 0x81e18 *)
eapply SRr_bind.
{ apply (HD g pos mf ly5 S5 W5 regs5 mem5 md5 HJ5 Hfr5 HK HPRE HG Hwok Hlen21 M5).
  - exact (je_vm_mf g pos mf ly2 S2 W2 regs2 mem2 md2 ly5 S5 W5 regs5 mem5 md5 176 _ HG K25
             ltac:(lia) ltac:(lia) V176).
  - rewrite (RK5 2%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rsp.
  - rewrite (RK5 9%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rs1.
  - rewrite (RK5 3%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rgp.
  - rewrite (RK5 4%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rtp.
  - rewrite (RK5 24%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact R24.
  - exact R23'. }
intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & K6 & Z1 & Z2 & BN & BD & R18').
pose proof (jeK_trans g pos mf ly2 S2 W2 regs2 mem2 md2 ly5 S5 W5 regs5 mem5 md5 ly6 S6 W6 regs6 mem6 md6
  K25 K6) as K26.
destruct K26 as (HJ6 & Hfr6 & HP6 & HK6 & RK6 & D6 & F6).
(* the close at 0x81e18 *)
apply SRr_ret.
apply (jcut_mk4 g pos mf nm tk dp (BASE + 0x170c) (Pj4 g pos mf) ly2 S2 W2 regs2 mem2 md2
  ly6 S6 W6 regs6 mem6 md6 HJ Hfrs HK MLE MOK HC HJC HJ6 Hfr6 HP6 HK6).
- intros r Hr. apply RK6. unfold JE_KEPT. cbn [In] in Hr |- *. tauto.
- exact D6.
- exact F6.
- unfold Pj4. refine (conj Hwok _).
  split; [rewrite (RK6 27%bv ltac:(unfold JE_KEPT; cbn; tauto)); exact R27|].
  split; [rewrite (RK6 26%bv ltac:(unfold JE_KEPT; cbn; tauto)); exact R26|].
  split; [rewrite (RK6 24%bv ltac:(unfold JE_KEPT; cbn; tauto)); exact R24|].
  split; [rewrite (RK6 25%bv ltac:(unfold JE_KEPT; cbn; tauto)); exact R25|].
  split; [exact R18'|]. split; [exact Hlen21|].
  split; [exact BN|]. split; [exact BD|]. split; [exact Z1 | exact Z2].
Qed.

End c.
End b.
End a.
