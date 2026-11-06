(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 996 of its 1063 lines of code are new or changed and 337 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE ODD LOOP,
   +0x408 .. +0x494, the phase `lf_ol` of lib/A/Prog/LLVMFuzzerTestOneInputDefs.v.

     lf_ol : forall POST, FROM POST CA -> forall j, 0 <= j < 4 -> FROM POST (OL j)

   Four turns. Turn j appends the odd table's entry 1 + j to g_nl's interface table:
   - +0x408 the instrumented check of odd[1 + j] (the eight bytes at LA_ODD + 8 + 8 j);
   - +0x414 .. +0x43c the check of if_name[n_if] and the store of the pointer odd[1 + j] there;
   - +0x440 .. +0x448 n_if := n_if + 1;
   - +0x44c .. +0x468 the check of if_index[n_if] and the store of 101 + j there;
   - +0x46c .. +0x47c a1 -= 8, a2 += 1, a7 += 1, a6 += 8, `bne a1, t0`: back to +0x408 for j < 3, else
     +0x480 `j +0x494` with `CA`.
   Each turn is one symbolic run from a state built at the turn's own numbers (the four turns are walked
   separately, so the loop's registers are the turn's literals and the run's tables reduce). The three
   instrumented checks leave three obligations, each the addressability of a range the kit pins at every
   allocator state: odd's by LLVMFuzzerTestOneInputSu.v `lf_zsh_odd_rd`, g_nl's two by LinkWalkZsh.v
   `zsh_gnl_rd`; so no error path is reached. The run makes no call.
   The sixteen bytes a turn writes (if_name[n_if], if_index[n_if], n_if) are all in g_nl, inside the ranges
   the invariant's zero clause already excludes, so every other clause is carried by
   lib/A/Prog/LLVMFuzzerTestOneInputKeep.v's transport lemmas; the interface table and `lf_ifp` grow by one
   entry, which is read off the odd table (`lf_odd_at`) and the two stores.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi LinkWalkZsh BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LLVMFuzzerTestOneInputDefs LLVMFuzzerTestOneInputSu LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputLp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The turn's numbers, its write set and the symbolic state it starts from
   ========================================================================== *)

Definition OL_AFL : Z := AF_LLVMFuzzerTestOneInput.
Definition OL_BR : Z := OL_AFL + 0x47c.      (* the back-edge test *)

Definition OL_A6 (j : Z) : Z := LA_ODD + 8 + 8 * j.
Definition OL_IFNo (j : Z) : Z := NK_IF_NAME + 8 * (60 + j).
Definition OL_IFIo (j : Z) : Z := NK_IF_INDEX + 4 * (60 + j).

(* the sixteen bytes a turn writes *)
Definition OL_X (j : Z) (a : Z) : Prop :=
  (LA_G_NL + OL_IFNo j <= a < LA_G_NL + OL_IFNo j + 8) \/
  (LA_G_NL + OL_IFIo j <= a < LA_G_NL + OL_IFIo j + 4) \/
  (LA_G_NL + NK_N_IF <= a < LA_G_NL + NK_N_IF + 4).

(* the bytes a turn may change as the memory view reads them: OL_X, and every address off the 64-bit range
   (the view reads such an address at its value mod 2^64, so the turn's writes reach it too) *)
Definition ol_XX (j a : Z) : Prop := ~ (0 <= a < 2 ^ 64) \/ OL_X j a.

Lemma ol_XX_not : forall j a, 0 <= a < 2 ^ 64 -> ~ OL_X j a -> ~ ol_XX j a.
Proof. intros j a Ha Hn [H | H]; [exact (H Ha) | exact (Hn H)]. Qed.

(* a run's frame extends the agreement of the memories off X, when X holds the run's windows *)
Lemma ol_kagree_step : forall segs E rs (m1 m2 m3 : word -> option byte) (X : Z -> Prop),
  kagree segs X m1 m2 -> frame_of E rs m2 m3 ->
  (forall a, ~ X a -> 0 <= a < 2 ^ 64) ->
  (forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> X a) ->
  kagree segs X m1 m3.
Proof.
  intros segs E rs m1 m2 m3 X H12 HF HX HW a Ha.
  rewrite <- (H12 a Ha). unfold mbyte. pose proof (HX a Ha) as Hr.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros Hin. exact (Ha (HW a Hr Hin)).
Qed.

(* the registers at the loop head: the turn's literals, g_nl's base in s2 (atom 18), the odd entry in a6
   (atom 16), the shadow base in s11 (atom 27), and a7 in the form the instrumented check of +0x408 is
   recognised in (LinkWalkPi.v denot_shadow_cell). *)
Definition OL_SHA : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 16 0) (SLit 3)) (SOff 27 0).
Definition ol_regs (j : Z) : list sv :=
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SLit (2 ^ 64 - 40); SOff 6 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SOff 10 0; SLit (2 ^ 64 - 8 - 8 * j); SLit (101 + j); SOff 18 0x42000;
   SLit NK_IF_NAME; SLit NK_IF_INDEX; SOff 16 0; OL_SHA; SOff 18 0; SOff 19 0;
   SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].

(* the four regions a turn touches: the odd entry it reads, and g_nl's three words *)
Definition ol_mem (j : Z) : smem :=
  [YP09.mkRegion (Some 16%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 18%nat) NK_N_IF (NK_N_IF + 4) NK_N_IF (NK_N_IF + 4)
     [YP09.mkChunk NK_N_IF (CVal 4 (SLit (60 + j)))];
   YP09.mkRegion (Some 18%nat) (OL_IFNo j) (OL_IFNo j + 8) (OL_IFNo j) (OL_IFNo j + 8) [];
   YP09.mkRegion (Some 18%nat) (OL_IFIo j) (OL_IFIo j + 4) (OL_IFIo j) (OL_IFIo j + 4) []].

Definition ol_facts (j : Z) : facts :=
  mkFacts [(16%nat, mkAF (OL_A6 j) (OL_A6 j) 3); (18%nat, mkAF LA_G_NL LA_G_NL 3);
           (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].

Definition ol_ss (j : Z) : sstate := mkSS LF_ol (ol_regs j) (ol_mem j) None (ol_facts j).
Definition OL_BX : sv := SOff 27 0.

(* the turn's numbers, by computation *)
Lemma ol_nums : forall j, 0 <= j < 4 ->
  0 < OL_A6 j /\ OL_A6 j + 8 <= LA_ODD + 48 /\ OL_A6 j mod 8 = 0 /\ OL_A6 j = LA_ODD + 8 * (j + 1) /\
  NK_IF_NAME <= OL_IFNo j /\ OL_IFNo j + 8 <= NK_IF_INDEX /\ OL_IFNo j mod 8 = 0 /\
  NK_IF_INDEX <= OL_IFIo j /\ OL_IFIo j + 4 <= NK_N_IF /\ NK_N_IF + 4 <= NK_SIZE.
Proof.
  intros j Hj. unfold OL_A6, OL_IFNo, OL_IFIo, LA_ODD, NK_IF_NAME, NK_IF_INDEX, NK_N_IF, NK_SIZE.
  split; [lia|]. split; [lia|].
  split; [replace (661344 + 8 + 8 * j) with ((82669 + j) * 8) by lia; apply Z_mod_mult|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [replace (271024 + 8 * (60 + j)) with ((33938 + j) * 8) by lia; apply Z_mod_mult|].
  split; [lia|]. split; lia.
Qed.
(* the back-edge test's own state: the two registers `bne` compares, no memory *)
Definition ol_regs_br (j : Z) : list sv :=
  sr_set (sr_set sr_atoms (5%bv : bv 5) (SLit (2 ^ 64 - 40))) (11%bv : bv 5)
    (SLit (2 ^ 64 - 16 - 8 * j)).
Definition ol_ss_br (j : Z) : sstate :=
  mkSS OL_BR (ol_regs_br j) [] None (mkFacts [(27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).

Lemma ol_nth_firstn : forall {A : Type} (l : list A) n k,
  (k < n)%nat -> nth_error (firstn n l) k = nth_error l k.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l k Hk; [lia|].
  destruct l as [|x l]; cbn [firstn]; [destruct k; reflexivity|].
  destruct k as [|k]; [reflexivity|]. cbn [nth_error]. apply IH. lia.
Qed.

(* the table has 60 + j entries at the head of turn j *)
Lemma ol_tab_len : forall j, 0 <= j <= 4 -> Z.of_nat (length (lf_tab_at (60 + j))) = 60 + j.
Proof.
  intros j Hj. replace (60 + j) with (Z.of_nat (Z.to_nat (60 + j))) by lia.
  rewrite (lf_tab_at_len (Z.to_nat (60 + j)) ltac:(lia)). reflexivity.
Qed.


Lemma ol_X_gnl : forall j a, 0 <= j < 4 -> OL_X j a -> LA_G_NL <= a < LA_G_NL + NK_SIZE.
Proof.
  intros j a Hj H. pose proof (ol_nums j Hj) as N.
  unfold OL_X, NK_SIZE, NK_N_IF, NK_IF_NAME, NK_IF_INDEX, OL_IFNo, OL_IFIo in *. lia.
Qed.

(* the ranges the invariant's zero clause excludes already cover the write set *)
Lemma ol_X_off : forall j a, 0 <= j < 4 -> OL_X j a ->
  exists q, a = LA_G_NL + q /\ 0 <= q < NK_SIZE /\
    ((NK_IF_NAME <= q < NK_IF_NAME + 640) \/ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) \/
     (NK_N_IF <= q < NK_N_IF + 4)).
Proof.
  intros j a Hj H. exists (a - LA_G_NL).
  unfold OL_X, OL_IFNo, OL_IFIo, NK_IF_NAME, NK_IF_INDEX, NK_N_IF, NK_SIZE in *.
  split; [lia|]. split; [lia|]. destruct H as [H | [H | H]]; [left | right; left | right; right]; lia.
Qed.

(* ==========================================================================
   2. Denotations of the registers the turn leaves
   ========================================================================== *)

Lemma ol_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof.
  intros E z. rewrite denot_lit_U, U_SLit. apply Z_to_bv64_eq_mod.
  unfold zcanon, M64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma ol_den_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros E n c v Hn Hv Hc. rewrite denot_lit_U. f_equal.
  rewrite (U_atom_off E n v c Hn ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma ol_den_a7 : forall E v base, ew E 16 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  ew E 27 = Z_to_bv 64 base -> 0 <= base -> base + v / 8 + 1 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD OL_SHA (SLit 1)) = Z_to_bv 64 (base + v / 8 + 1).
Proof.
  intros E v base H16 Hv H27 Hb Hs. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= v / 8) by (apply Z.div_pos; lia).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 1) with 1.
  unfold OL_SHA.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E 16 v 0 H16 ltac:(lia) ltac:(lia)), (U_atom_off E 27 base 0 H27 ltac:(lia) ltac:(lia)).
  rewrite !Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64.
  rewrite ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

(* the image instance's facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

(* ==========================================================================
   3. Where the written bytes are NOT
   ========================================================================== *)

Lemma ol_gnl_not_ro : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros a Ha. rewrite HSEGS. apply LA_G_not_ro. unfold inG. apply Exists_exists.
  exists (LA_G_NL, 271992). split; [cbn [LA_G In]; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. unfold NK_SIZE in Ha. lia.
Qed.

Lemma ol_blk_not_gnl : forall ly S (W : world SEGS) mem md b n a,
  AR SEGS B ly S W mem md -> In (b, n) (ablocks B ly S) ->
  b <= a -> (a < b + 1304 \/ a < b + req_size n) ->
  0 <= a < 2 ^ 64 /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE).
Proof.
  intros ly S W mem md b n a HAR Hin Hlo Hhi.
  pose proof (blk_off_imgP B ly S W mem md b n HAR Hin) as Hoff.
  pose proof (al_blocks SEGS B LAWS ly S W mem md b n HAR Hin)
    as (Hmod & H4096 & Hce & Hin_app & Hpr & Hpw & Hnr).
  pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_NL, NK_SIZE in *. split; lia.
Qed.

Lemma ol_amf_not_gnl : forall ly S (W : world SEGS) mem md T3 a,
  MS = link_amf -> AR SEGS B ly S W mem md -> incl T3 (ablocks B ly S) ->
  amf_fp MS T3 a -> 0 <= a < 2 ^ 64 /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE).
Proof.
  intros ly S W mem md T3 a HMS HAR Hincl Ha.
  destruct Ha as [Hh | [He | (f & n & Hin & Hf)]].
  - rewrite HMS in Hh.
    cbv [amf_head_addr amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Hh.
    unfold LA_G_NL, NK_SIZE. split; lia.
  - rewrite HMS in He.
    cbv [amf_env_addr amf_threaded amf_need_locks amf_ofl_lock link_amf] in He.
    unfold LA_G_NL, NK_SIZE. split; lia.
  - pose proof (Hincl _ Hin) as Hb.
    apply (ol_blk_not_gnl ly S W mem md f n a HAR Hb);
      [unfold AMF_BLOCK in Hf; lia | left; unfold AMF_BLOCK in Hf; lia].
Qed.

(* ==========================================================================
   4. g_nl's byte list after the turn
   ========================================================================== *)

Lemma ol_nlk_after : forall (m m' : word -> option byte) bs,
  anlk_at SEGS m LA_G_NL bs -> mem_grows m m' ->
  anlk_at SEGS m' LA_G_NL (abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)).
Proof.
  intros m m' bs (((Hb0 & Hb1 & Hb) & Hw) & Hl) Hg.
  assert (Hpres : forall i, (i < Z.to_nat NK_SIZE)%nat -> exists c, mbyte SEGS m' (LA_G_NL + Z.of_nat i) = Some c).
  { intros i Hi. pose proof (Hb i ltac:(lia)) as E.
    destruct (nth_error bs i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    unfold mbyte in *.
    destruct (m' (Z_to_bv 64 (LA_G_NL + Z.of_nat i))) as [c'|] eqn:E'; [exists c'; reflexivity|].
    destruct (m (Z_to_bv 64 (LA_G_NL + Z.of_nat i))) as [c0|] eqn:E0.
    - exfalso. exact (Hg _ ltac:(rewrite E0; discriminate) E').
    - exists c. exact E. }
  split; [split|].
  - split; [unfold LA_G_NL; lia|]. split.
    + rewrite abytes_of_length. unfold LA_G_NL, NK_SIZE. lia.
    + intros i Hi. rewrite abytes_of_length in Hi.
      destruct (Hpres i Hi) as (c & Hc). rewrite Hc. symmetry. apply abytes_of_nth; [exact Hi | exact Hc].
  - rewrite abytes_of_length. intros i Hi.
    apply (writable_at_grows SEGS m m' (LA_G_NL + i) Hg). apply Hw. rewrite Hl. unfold NK_SIZE in *. lia.
  - rewrite abytes_of_length. unfold NK_SIZE. lia.
Qed.

Lemma ol_fld_of_val : forall (m : word -> option byte) off (n : nat) v,
  0 <= off -> off + Z.of_nat n <= NK_SIZE -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m (LA_G_NL + off) n v ->
  rdn (abytes_of SEGS m LA_G_NL (Z.to_nat NK_SIZE)) off (Z.of_nat n) = v.
Proof.
  intros m off n v H0 H1 Hv Hval.
  apply (rdn_of_vals _ off n v H0); [rewrite abytes_of_length; unfold NK_SIZE in *; lia | exact Hv|].
  intros k Hk. apply abytes_of_nth; [unfold NK_SIZE in *; lia|].
  replace (LA_G_NL + Z.of_nat (Z.to_nat off + k)) with (LA_G_NL + off + Z.of_nat k) by lia.
  exact (Hval k Hk).
Qed.

(* ==========================================================================
   5. The state the turn runs from
   ========================================================================== *)

(* the environment: the registers at the loop head, then the odd entry's pointer *)
Definition ol_E (regs : bvmap 5 word) (q : Z) : env := Eimg (Ereg regs [Z_to_bv 64 q]).

Lemma ol_E_reg : forall regs q n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ol_E regs q) n = getr regs r.
Proof. intros regs q n r Hn. exact (ew_Eimg_Ereg_nat regs _ n r Hn). Qed.

Lemma ol_E_q : forall regs q, ew (ol_E regs q) 32 = Z_to_bv 64 q.
Proof.
  intros regs q. unfold ol_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs [Z_to_bv 64 q] 0).
Qed.

Lemma ol_E_img : forall regs q, img_env pa_val A_LIM (ol_E regs q).
Proof. intros regs q. unfold ol_E. apply Eimg_env. Qed.

(* the machine state at a cut has the shape st_ok_pi asks for *)
Lemma ol_ms_shape : forall (fy : YK11.FPState) pc (ms : machine_state) (H : word -> bool),
  lf_shape fy pc ms -> restrict H ms = @YK11.mkst fy (ms_regs ms) (w64 (BASE + pc)) (mrestrict H (ms_mem ms)) (seg_rom SEGS).
Proof.
  intros fy pc ms H (H1 & H2 & H3 & H4 & H5 & H6). destruct ms. cbn in *. subst. reflexivity.
Qed.

(* four bytes of a byte list, as the value the engine's chunk holds *)
Lemma ol_val4 : forall (m : word -> option byte) a b0 b1 b2 b3,
  abytes SEGS m a [b0; b1; b2; b3] -> val_mem SEGS m a 4 (bytes_le_to_Z [b0; b1; b2; b3]).
Proof.
  intros m a b0 b1 b2 b3 (Ha0 & Ha1 & Hb).
  pose proof (u8_range b0) as R0. pose proof (u8_range b1) as R1.
  pose proof (u8_range b2) as R2. pose proof (u8_range b3) as R3.
  assert (Hv : bytes_le_to_Z [b0; b1; b2; b3] =
      bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
  { rewrite !bytes_le_to_Z_cons. cbn [bytes_le_to_Z]. lia. }
  set (v := bytes_le_to_Z [b0; b1; b2; b3]) in *.
  assert (Hvr : 0 <= v < 2 ^ (8 * Z.of_nat 4)) by (cbn [Z.of_nat Z.mul]; lia).
  intros k Hk. rewrite (Hb k ltac:(cbn [length]; lia)).
  rewrite (le_byte_small v 4 k Hvr Hk).
  destruct k as [|[|[|[|k]]]]; cbn [nth_error]; [ | | | | cbn [length] in Hk; lia ];
    f_equal; apply (proj2 (bv_eq _ _ _)); rewrite Z_to_bv_unsigned;
    unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256;
    rewrite Z.shiftr_div_pow2 by lia.
  - change (8 * Z.of_nat 0) with 0. change (2 ^ 0) with 1. rewrite Z.div_1_r, Hv. lia.
  - change (8 * Z.of_nat 1) with 8. change (2 ^ 8) with 256. rewrite Hv. lia.
  - change (8 * Z.of_nat 2) with 16. change (2 ^ 16) with 65536. rewrite Hv. lia.
  - change (8 * Z.of_nat 3) with 24. change (2 ^ 24) with 16777216. rewrite Hv. lia.
Qed.

(* a four-byte field of g_nl, from the byte list the invariant carries *)
Lemma ol_nlk_field : forall (m : word -> option byte) bs off,
  anlk_at SEGS m LA_G_NL bs -> 0 <= off -> off + 4 <= NK_SIZE ->
  val_mem SEGS m (LA_G_NL + off) 4 (rdn bs off 4).
Proof.
  intros m bs off ((Hb & Hw) & Hl) H0 H1.
  pose proof Hb as (Hz0 & Hz1 & Hnth).
  assert (Hget : forall i, 0 <= i < 4 -> exists c, nth_error bs (Z.to_nat off + Z.to_nat i) = Some c /\
            mbyte SEGS m (LA_G_NL + off + i) = Some c).
  { intros i Hi.
    destruct (nth_error bs (Z.to_nat off + Z.to_nat i)) as [c|] eqn:Ec;
      [|apply nth_error_None in Ec; lia].
    exists c. split; [reflexivity|].
    rewrite <- Ec. replace (LA_G_NL + off + i) with (LA_G_NL + Z.of_nat (Z.to_nat off + Z.to_nat i)) by lia.
    apply Hnth. lia. }
  destruct (Hget 0 ltac:(lia)) as (c0 & E0 & M0). destruct (Hget 1 ltac:(lia)) as (c1 & E1 & M1).
  destruct (Hget 2 ltac:(lia)) as (c2 & E2 & M2). destruct (Hget 3 ltac:(lia)) as (c3 & E3 & M3).
  assert (Hsl : slice bs off 4 = [c0; c1; c2; c3]).
  { apply lw_list_ext; [rewrite lw_slice_length by lia; reflexivity|].
    intros k Hk. rewrite lw_slice_length in Hk by lia. rewrite lw_slice_nth by lia.
    destruct k as [|[|[|[|k]]]]; cbn [nth_error];
      [ rewrite <- E0 | rewrite <- E1 | rewrite <- E2 | rewrite <- E3 | cbn in Hk; lia ];
      f_equal; lia. }
  unfold rdn. rewrite Hsl.
  apply ol_val4. split; [unfold LA_G_NL in *; lia|]. split; [cbn [length]; unfold LA_G_NL, NK_SIZE in *; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|i]]]]; cbn [nth_error];
    [ replace (LA_G_NL + off + Z.of_nat 0) with (LA_G_NL + off + 0) by lia; exact M0
    | replace (LA_G_NL + off + Z.of_nat 1) with (LA_G_NL + off + 1) by lia; exact M1
    | replace (LA_G_NL + off + Z.of_nat 2) with (LA_G_NL + off + 2) by lia; exact M2
    | replace (LA_G_NL + off + Z.of_nat 3) with (LA_G_NL + off + 3) by lia; exact M3
    | lia ].
Qed.

(* the regions of a turn are well formed *)
Lemma ol_regions_wf : forall j, 0 <= j < 4 -> regions_wf (ol_mem j) = true.
Proof.
  intros j Hj. assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct H as [ -> | [ -> | [ -> | -> ] ] ]; vm_compute; reflexivity.
Qed.

Lemma ol_set_lit : forall (fy : YK11.FPState) E ss ms (r : bv 5) z v,
  @st_ok_pi SEGS pa_val fy E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = w64 v ->
  z mod 2 ^ 64 = v mod 2 ^ 64 ->
  @st_ok_pi SEGS pa_val fy E
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros fy E ss ms r z v HS Hr Hv Hz. apply (st_ok_pi_set_reg (fx := fy)); [exact HS | exact Hr|].
  rewrite Hv, ol_den_lit. apply Z_to_bv64_eq_mod. symmetry. exact Hz.
Qed.

(* THE STATE a turn runs from *)
Lemma ol_entry : forall (fy : YK11.FPState) j q kbs (W3 : world SEGS) (ms3 : machine_state),
  0 <= j < 4 -> 0 <= q < 2 ^ 64 ->
  lf_shape fy LF_ol ms3 ->
  getr (ms_regs ms3) 5 = w64 (- 0x28) ->
  getr (ms_regs ms3) 11 = w64 (- 8 - 8 * j) ->
  getr (ms_regs ms3) 12 = w64 (101 + j) ->
  getr (ms_regs ms3) 13 = w64 (LA_G_NL + 0x42000) ->
  getr (ms_regs ms3) 14 = w64 0x422b0 ->
  getr (ms_regs ms3) 15 = w64 0x42530 ->
  getr (ms_regs ms3) 16 = w64 (OL_A6 j) ->
  getr (ms_regs ms3) 17 = w64 (SHADOW_OFF + OL_A6 j / 8) ->
  getr (ms_regs ms3) 18 = w64 LA_G_NL ->
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs ->
  nk_n_if kbs = 60 + j ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) (OL_A6 j) q ->
  @st_ok_pi SEGS pa_val fy (ol_E (ms_regs ms3) q) (ol_ss j) (restrict (w_H W3) ms3).
Proof.
  intros fy j q kbs W3 ms3 Hj Hq HSH H5 H11 H12 H13 H14 H15 H16 H17 H18 H27 HNLK HNIF HQ.
  pose proof (ol_nums j Hj) as N.
  pose proof HNLK as ((HNb & HNw) & HNl).
  set (E := ol_E (ms_regs ms3) q) in *.
  assert (E16 : ew E 16 = w64 (OL_A6 j))
    by (unfold E; rewrite (ol_E_reg _ q 16%nat (16%bv : bv 5) eq_refl); exact H16).
  assert (E18 : ew E 18 = w64 LA_G_NL)
    by (unfold E; rewrite (ol_E_reg _ q 18%nat (18%bv : bv 5) eq_refl); exact H18).
  assert (E27 : ew E 27 = w64 SHADOW_OFF)
    by (unfold E; rewrite (ol_E_reg _ q 27%nat (27%bv : bv 5) eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 q) by (unfold E; apply ol_E_q).
  assert (U16 : bv_unsigned (ew E 16) = OL_A6 j)
    by (rewrite E16; apply unsigned_lit_small; unfold OL_A6, LA_ODD in *; lia).
  assert (U18 : bv_unsigned (ew E 18) = LA_G_NL)
    by (rewrite E18; apply unsigned_lit_small; unfold LA_G_NL; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
    by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  rewrite (ol_ms_shape fy LF_ol ms3 (w_H W3) HSH).
  assert (HS0 : @st_ok_pi SEGS pa_val fy E (mkSS LF_ol sr_atoms (ol_mem j) None (ol_facts j))
    (@YK11.mkst fy (ms_regs ms3) (w64 (BASE + LF_ol)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - unfold E, ol_E. apply regs_ok_Eimg_Ereg.
    - apply ol_regions_wf. exact Hj.
    - unfold ol_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U16. split; [unfold OL_A6, LA_ODD in *; lia|].
        split; [unfold OL_A6, LA_ODD in *; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (OL_A6 j) 0 8 (SOff 32 0) q);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn [Z.of_N Z.mul]; lia | cbn [Z.of_N]; lia |].
        rewrite Z.add_0_r. exact HQ.
      + rewrite U18. split; [unfold LA_G_NL, NK_N_IF; lia|].
        split; [unfold LA_G_NL, NK_N_IF; lia|].
        split; [intros o Ho; apply HNw; rewrite HNl; unfold NK_N_IF, NK_SIZE in *; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ LA_G_NL NK_N_IF 4 (SLit (60 + j)) (60 + j));
          [apply ol_den_lit | cbn [Z.of_N Z.mul]; lia | cbn [Z.of_N]; lia |].
        rewrite <- HNIF. unfold nk_n_if, fld_u32.
        apply (ol_nlk_field _ kbs NK_N_IF HNLK); unfold NK_N_IF, NK_SIZE; lia.
      + rewrite U18. split; [unfold LA_G_NL, OL_IFNo, NK_IF_NAME in *; lia|].
        split; [unfold LA_G_NL, OL_IFNo, NK_IF_NAME in *; lia|].
        split; [intros o Ho; apply HNw; rewrite HNl;
                unfold OL_IFNo, NK_IF_NAME, NK_SIZE in *; lia | constructor].
      + rewrite U18. split; [unfold LA_G_NL, OL_IFIo, NK_IF_INDEX in *; lia|].
        split; [unfold LA_G_NL, OL_IFIo, NK_IF_INDEX in *; lia|].
        split; [intros o Ho; apply HNw; rewrite HNl;
                unfold OL_IFIo, NK_IF_INDEX, NK_SIZE in *; lia | constructor].
    - apply pairwise_disjoint_of_extents. unfold ol_mem, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U16, U18.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold OL_A6, OL_IFNo, OL_IFIo, LA_ODD, LA_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_N_IF in *.
      repeat split; lia.
    - unfold ol_facts. split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U16, U18, U27.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end;
        first [ lia
              | unfold LA_G_NL; change (2 ^ 3) with 8; reflexivity
              | unfold OL_A6, LA_ODD; change (2 ^ 3) with 8;
                replace (661344 + 8 + 8 * j) with ((82669 + j) * 8) by lia; apply Z_mod_mult ]. }
  pose proof (ol_set_lit fy E _ _ (5%bv : bv 5) (2 ^ 64 - 40) (- 0x28) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; exact H5) ltac:(lia)) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  pose proof (ol_set_lit fy E _ _ (11%bv : bv 5) (2 ^ 64 - 8 - 8 * j) (- 8 - 8 * j) HS1 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; exact H11) ltac:(lia)) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (ol_set_lit fy E _ _ (12%bv : bv 5) (101 + j) (101 + j) HS2 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; exact H12) ltac:(reflexivity)) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  pose proof (st_ok_pi_set_reg (fx := fy) E _ _ (13%bv : bv 5) (SOff 18 0x42000) HS3 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; rewrite H13; symmetry;
          apply (ol_den_off E 18%nat 0x42000 LA_G_NL E18); unfold LA_G_NL; lia)) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
  pose proof (ol_set_lit fy E _ _ (14%bv : bv 5) NK_IF_NAME 0x422b0 HS4 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; exact H14) ltac:(reflexivity)) as HS5.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5.
  pose proof (ol_set_lit fy E _ _ (15%bv : bv 5) NK_IF_INDEX 0x42530 HS5 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; exact H15) ltac:(reflexivity)) as HS6.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6.
  pose proof (st_ok_pi_set_reg (fx := fy) E _ _ (17%bv : bv 5) OL_SHA HS6 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; rewrite H17; symmetry; unfold OL_SHA;
          apply (denot_shadow_cell E 16%nat 27%nat (OL_A6 j) SHADOW_OFF E16);
          first [ exact E27 | unfold OL_A6, LA_ODD, SHADOW_OFF in *; lia ])) as HS7.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS7.
  exact HS7.
Qed.

(* ==========================================================================
   6. What a turn writes, and what it leaves alone
   ========================================================================== *)

(* the sixteen bytes miss every footprint the cut's other clauses read *)
Lemma ol_X_miss_jbk : forall cx T3 ly3 S3 (W3 : world SEGS) mem md3 j a,
  0 <= j < 4 -> MS = link_amf -> la_nul = LA_NUL ->
  AR SEGS B ly3 S3 W3 mem md3 -> incl T3 (ablocks B ly3 S3) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  lf_jbk_fp MS la_nul cx T3 a -> ~ ol_XX j a.
Proof.
  intros cx T3 ly3 S3 W3 mem md3 j a Hj HMS HLN HAR Hincl Hpl Ha.
  assert (HR : 0 <= a < 2 ^ 64 /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE)).
  { destruct Ha as [Hamf | [Hln | [Hro | Hp]]].
    - exact (ol_amf_not_gnl ly3 S3 W3 mem md3 T3 a HMS HAR Hincl Hamf).
    - rewrite HLN in Hln. unfold LA_NUL, LA_LONG_ALIAS, LA_G_NL, NK_SIZE in *. split; lia.
    - pose proof (in_roP_low a Hro) as Hlow. unfold kLowMemEnd in Hlow.
      split; [lia | intros HG; exact (ol_gnl_not_ro a HG Hro)].
    - assert (Hn : 0 < c_n cx) by lia.
      pose proof (al_blocks SEGS B LAWS ly3 S3 W3 mem md3 (c_p cx) (c_n cx) HAR (Hpl Hn))
        as (_ & _ & _ & _ & _ & _ & Hnr).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2).
      exact (ol_blk_not_gnl ly3 S3 W3 mem md3 (c_p cx) (c_n cx) a HAR (Hpl Hn)
               ltac:(lia) ltac:(right; lia)). }
  destruct HR as (HR1 & HR2). apply ol_XX_not; [exact HR1|].
  intros HX. exact (HR2 (ol_X_gnl j a Hj HX)).
Qed.

(* the frame's bytes are above the allocator's ceiling, g_nl's are below it *)
Lemma ol_X_miss_frame : forall cx fp ly3 S3 (W3 : world SEGS) mem md3 j a,
  0 <= j < 4 -> AR SEGS B ly3 S3 W3 mem md3 -> In (LF_CID, fp) (frames S3) ->
  frame_addr ly3 LF_CID fp = frame_addr (c_ly cx) LF_CID fp ->
  alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK -> 0 <= spZ (c_regs cx) - LF_MFRAME ->
  spZ (c_regs cx) mod 16 = 0 -> spZ (c_regs cx) <= 2 ^ 47 ->
  (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
   lf_cur_fp cx a) ->
  ~ ol_XX j a.
Proof.
  intros cx fp ly3 S3 W3 mem md3 j a Hj HAR Hin HFA Hce H0 H16 H47 Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (lf_sp1_range (spZ (c_regs cx)) H0 H16) as (Hs1 & _ & _).
  pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem md3 LF_CID fp HAR Hin) as (Hf1 & Hf2 & _).
  pose proof (fs_frame_bytes_nonneg LF_CID) as Hfb.
  pose proof (frm_off_imgP B ly3 S3 W3 mem md3 LF_CID fp HAR Hin) as Hoff.
  rewrite HFA in Hf1, Hf2, Hoff.
  set (F := frame_addr (c_ly cx) LF_CID fp) in *.
  assert (HF8 : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (HR : 0 <= a < 2 ^ 64 /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE)).
  { unfold lf_saved_fp, lf_header_fp, lf_fshadow_fp, lf_slots_fp, lf_cur_fp, lf_sp1, lf_SH, lf_F,
      shadow_of_addr, SHADOW_OFF, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP,
      LA_G_NL, NK_SIZE, LF_MFRAME, LLVMF_STK in *.
    fold F in Ha.
    destruct Ha as [H | [H | [H | [H | H]]]]; split; lia. }
  destruct HR as (HR1 & HR2). apply ol_XX_not; [exact HR1|].
  intros HX. exact (HR2 (ol_X_gnl j a Hj HX)).
Qed.

(* the spill slots the set-up cut carries, and the odd table's slot *)
Definition ol_slots (cx : lcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  lf_slot cx W3 ms3 LS_SHB SHADOW_OFF /\ lf_slot cx W3 ms3 LS_FK (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_F (lf_F cx fp) /\ lf_slot cx W3 ms3 LS_F0 (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_WA (lf_F cx fp + LO_WA) /\ lf_slot cx W3 ms3 LS_B160 (lf_F cx fp + LO_B160) /\
  lf_slot cx W3 ms3 LS_B1A0 (lf_F cx fp + LO_B1A0) /\ lf_slot cx W3 ms3 LS_B2E0 (lf_F cx fp + LO_B2E0) /\
  lf_slot cx W3 ms3 LS_B330 (lf_F cx fp + LO_B330) /\ lf_slot cx W3 ms3 LS_ODD LA_ODD.

Lemma ol_slots_keep : forall X cx fp W3 ms3 W3' ms3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall a, lf_slots_fp cx a -> ~ X a) ->
  ol_slots cx fp W3 ms3 -> ol_slots cx fp W3' ms3'.
Proof.
  intros X cx fp W3 ms3 W3' ms3' HK HX H. unfold ol_slots in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat split;
    (eapply (lf_slot_keep X cx W3 ms3 W3' ms3'); [exact HK | | eassumption];
     intros i Hi; apply HX; unfold lf_slots_fp, LS_SHB, LS_FK, LS_F, LS_F0, LS_WA, LS_B160, LS_B1A0,
       LS_B2E0, LS_B330, LS_ODD in *; lia).
Qed.

(* the interface table after the turn: the entries so far, and the new one *)
Lemma ol_tab_step : forall (m m' : word -> option byte) j kbs kbs' q,
  0 <= j < 4 -> kagree SEGS (ol_XX j) m m' ->
  anlk_at SEGS m LA_G_NL kbs ->
  aiftab_at SEGS m LA_G_NL kbs (lf_tab_at (60 + j)) ->
  lf_ifp m (60 + j) -> lf_gnames_at 64 m -> lf_odd_at m ->
  nk_n_if kbs' = 61 + j ->
  au64_at SEGS m' (LA_G_NL + OL_IFNo j) q ->
  au32_at SEGS m' (LA_G_NL + OL_IFIo j) (101 + j) ->
  au64_at SEGS m (OL_A6 j) q -> q <> 0 ->
  acstr_at SEGS m q (nth (Z.to_nat (1 + j)) lf_odd_strs []) ->
  (forall i, 0 <= i <= Z.of_nat (length (nth (Z.to_nat (1 + j)) lf_odd_strs [])) ->
     in_roP SEGS PCAP_RLO PCAP_RHI (q + i)) ->
  aiftab_at SEGS m' LA_G_NL kbs' (lf_tab_at (61 + j)) /\ lf_ifp m' (61 + j).
Proof.
  intros m m' j kbs kbs' q Hj HK HNLK HIFT HIFP HGN HOD HN' HSN HSI HQ HQ0 HQS HQRO.
  pose proof (ol_nums j Hj) as N.
  assert (XR : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ ol_XX j a).
  { intros a Ha. pose proof (in_roP_low a Ha) as Hlow. unfold kLowMemEnd in Hlow.
    apply ol_XX_not; [lia|]. intros HX. exact (ol_gnl_not_ro a (ol_X_gnl j a Hj HX) Ha). }
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ ol_XX j a)
    by (intros a Ha; apply ol_XX_not; [unfold LA_G_NAMES, G_NAMES_SIZE in *; lia|];
        intros HX; pose proof (ol_X_gnl j a Hj HX);
        unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE in *; lia).
  assert (XG : forall k, 0 <= k < 8 -> forall e, 0 <= e < 60 + j ->
            ~ ol_XX j (LA_G_NL + NK_IF_NAME + 8 * e + k)).
  { intros k Hk e He. apply ol_XX_not; [unfold LA_G_NL, NK_IF_NAME; lia|].
    intros HX. pose proof (ol_X_gnl j _ Hj HX).
    unfold OL_X, OL_IFNo, OL_IFIo, NK_IF_NAME, NK_IF_INDEX, NK_N_IF in *. lia. }
  assert (XI : forall k, 0 <= k < 4 -> forall e, 0 <= e < 60 + j ->
            ~ ol_XX j (LA_G_NL + NK_IF_INDEX + 4 * e + k)).
  { intros k Hk e He. apply ol_XX_not; [unfold LA_G_NL, NK_IF_INDEX; lia|].
    intros HX. pose proof (ol_X_gnl j _ Hj HX).
    unfold OL_X, OL_IFNo, OL_IFIo, NK_IF_NAME, NK_IF_INDEX, NK_N_IF in *. lia. }
  assert (HPL : forall (i : nat) nm ix p, (i < Z.to_nat (60 + j))%nat ->
            nth_error lf_tab i = Some (nm, ix) -> au64_at SEGS m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
            acstr_at SEGS m p nm -> forall k, 0 <= k <= Z.of_nat (length nm) -> ~ ol_XX j (p + k)).
  { intros i nm ix p Hi Hnth Hp Hs k Hk.
    destruct (lf_tab_entry i nm ix Hnth) as (H64 & Hlt & Hge).
    destruct (HIFP (Z.of_nat i) ltac:(lia)) as (qq & Hqq & Hq1 & Hq2).
    pose proof (val_mem8_mod SEGS m _ p qq Hp Hqq) as Epq.
    pose proof Hs as ((Hp0 & Hp1 & _) & _). rewrite length_app in Hp1. cbn [length] in Hp1.
    destruct (Nat.lt_ge_cases i 60) as [Hi60 | Hi60].
    - rewrite (Hq1 ltac:(lia)) in Epq. pose proof (Hlt Hi60) as Hlen.
      assert (Hd : 0 <= Z.of_nat i / 15 <= 3) by lia.
      rewrite (Z.mod_small p) in Epq by lia.
      rewrite Z.mod_small in Epq by (unfold LA_G_NAMES; lia).
      apply XN. unfold G_NAMES_SIZE. lia.
    - pose proof (Hge Hi60) as Hnm.
      destruct (HOD (i - 59)%nat ltac:(lia)) as (q' & Hq' & Hq'0 & Hs' & Hro).
      assert (Eq : qq mod 2 ^ 64 = q' mod 2 ^ 64).
      { apply (val_mem8_mod SEGS m (LA_ODD + 8 * Z.of_nat (i - 59))); [|exact Hq'].
        replace (Z.of_nat (i - 59)) with (Z.of_nat i - 59) by lia. exact (Hq2 ltac:(lia)). }
      pose proof Hs' as ((Hq'a & Hq'b & _) & _). rewrite length_app in Hq'b. cbn [length] in Hq'b.
      rewrite (Z.mod_small p) in Epq by lia. rewrite (Z.mod_small q') in Eq by lia.
      assert (Ep : p = q') by (rewrite Epq; exact Eq).
      rewrite Ep. apply XR. apply Hro. rewrite <- Hnm. exact Hk. }
  pose proof HIFT as (HN & H80 & HT).
  assert (HPREF : forall (i : nat), (i < Z.to_nat (60 + j))%nat ->
            nth_error (lf_tab_at (60 + j)) i = nth_error (lf_tab_at (61 + j)) i).
  { intros i Hi. unfold lf_tab_at.
    rewrite (ol_nth_firstn lf_tab (Z.to_nat (60 + j)) i Hi).
    rewrite (ol_nth_firstn lf_tab (Z.to_nat (61 + j)) i ltac:(lia)). reflexivity. }
  assert (HNEW : nth_error (lf_tab_at (61 + j)) (Z.to_nat (60 + j)) =
                 Some (nth (Z.to_nat (1 + j)) lf_odd_strs [], 101 + j)).
  { unfold lf_tab_at.
    rewrite (ol_nth_firstn lf_tab (Z.to_nat (61 + j)) (Z.to_nat (60 + j)) ltac:(lia)).
    rewrite (lf_tab_nth_o (Z.to_nat (60 + j)) ltac:(lia)).
    f_equal. f_equal; [f_equal; lia | lia]. }
  split.
  - assert (HL1 : Z.of_nat (length (lf_tab_at (61 + j))) = 61 + j)
      by (replace (61 + j) with (60 + (j + 1)) by lia; apply ol_tab_len; lia).
    split; [rewrite HN', HL1; reflexivity|].
    split; [rewrite HL1; lia|].
    intros i nm ix Hi.
    destruct (Nat.lt_ge_cases i (Z.to_nat (60 + j))) as [Hlt | Hge].
    + rewrite <- (HPREF i Hlt) in Hi.
      destruct (HT i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
      assert (Hnth : nth_error lf_tab i = Some (nm, ix))
        by (rewrite <- Hi; unfold lf_tab_at; symmetry; apply ol_nth_firstn; lia).
      split; [exact Hix|]. exists p. split; [|split; [exact Hp0 | split]].
      * apply (au64_keep SEGS (ol_XX j) m m' _ p HK); [|exact Hp].
        intros k Hk. apply (XG k Hk (Z.of_nat i)). lia.
      * apply (acstr_keep SEGS (ol_XX j) m m' p nm HK); [|exact Hs].
        exact (HPL i nm ix p Hlt Hnth Hp Hs).
      * apply (au32_keep SEGS (ol_XX j) m m' _ ix HK); [|exact Hx].
        intros k Hk. apply (XI k Hk (Z.of_nat i)). lia.
    + assert (Hib : (i < Z.to_nat (61 + j))%nat).
      { destruct (Nat.lt_ge_cases i (Z.to_nat (61 + j))) as [HA | HA]; [exact HA|].
        exfalso. assert (Hn : nth_error (lf_tab_at (61 + j)) i = None)
          by (apply nth_error_None; lia).
        rewrite Hn in Hi. discriminate. }
      assert (Hie : i = Z.to_nat (60 + j)) by lia. subst i.
      rewrite HNEW in Hi. injection Hi as <- <-.
      split; [lia|]. exists q. split; [|split; [exact HQ0 | split]].
      * replace (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat (Z.to_nat (60 + j)))
          with (LA_G_NL + OL_IFNo j) by (unfold OL_IFNo; lia). exact HSN.
      * apply (acstr_keep SEGS (ol_XX j) m m' q _ HK); [|exact HQS].
        intros k Hk. exact (XR (q + k) (HQRO k Hk)).
      * replace (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat (Z.to_nat (60 + j)))
          with (LA_G_NL + OL_IFIo j) by (unfold OL_IFIo; lia). exact HSI.
  - intros e He. destruct (Z.lt_ge_cases e (60 + j)) as [Hlt | Hge].
    + destruct (HIFP e ltac:(lia)) as (p & Hp & Hp1 & Hp2). exists p.
      split; [|split].
      * apply (au64_keep SEGS (ol_XX j) m m' _ p HK); [|exact Hp].
        intros k Hk. apply (XG k Hk e). lia.
      * exact Hp1.
      * intros He60. apply (au64_keep SEGS (ol_XX j) m m' _ p HK); [|exact (Hp2 He60)].
        intros k Hk. apply XR. right. unfold LA_ODD, PCAP_RLO, PCAP_RHI in *. lia.
    + assert (He' : e = 60 + j) by lia. subst e. exists q. split; [|split].
      * replace (LA_G_NL + NK_IF_NAME + 8 * (60 + j)) with (LA_G_NL + OL_IFNo j)
          by (unfold OL_IFNo; lia). exact HSN.
      * intros Hc. lia.
      * intros _.
        replace (LA_ODD + 8 * (60 + j - 59)) with (OL_A6 j) by (unfold OL_A6; lia).
        apply (au64_keep SEGS (ol_XX j) m m' _ q HK); [|exact HQ].
        intros k Hk. apply XR. right. unfold OL_A6, LA_ODD, PCAP_RLO, PCAP_RHI in *. lia.
Qed.

(* a four-byte field the zero clause covers *)
Lemma ol_zero4 : forall (m : word -> option byte) off,
  (forall r, off <= r < off + 4 -> val_mem SEGS m (LA_G_NL + r) 1 0) ->
  val_mem SEGS m (LA_G_NL + off) 4 0.
Proof.
  intros m off HZ k Hk.
  rewrite (le_byte_small 0 4%nat k ltac:(change (8 * Z.of_nat 4) with 32; lia) Hk), Z.shiftr_0_l.
  pose proof (HZ (off + Z.of_nat k) ltac:(lia) 0%nat ltac:(lia)) as HB.
  rewrite (le_byte_small 0 1%nat 0%nat ltac:(change (8 * Z.of_nat 1) with 8; lia) ltac:(lia)),
          Z.shiftr_0_l in HB.
  replace (LA_G_NL + (off + Z.of_nat k) + Z.of_nat 0) with (LA_G_NL + off + Z.of_nat k) in HB by lia.
  exact HB.
Qed.

(* THE CUT after the turn: every memory clause of the set-up cut, and the grown table *)
Lemma ol_core_next : forall (fy : YK11.FPState) cx fp k2 ly3 S3 (W3 : world SEGS) (ms3 ms4 : machine_state)
    md3 md4 j kbs q pc,
  0 <= j < 4 -> MS = link_amf -> la_nul = LA_NUL ->
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 -> In (LF_CID, fp) (frames S3) ->
  alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK ->
  0 <= spZ (c_regs cx) - LF_MFRAME -> spZ (c_regs cx) mod 16 = 0 -> spZ (c_regs cx) <= 2 ^ 47 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  lf_setup_inv B MT MS la_nul LF_ol cx fy fp k2 ly3 S3 W3 ms3 md3 ->
  lf_slot cx W3 ms3 LS_ODD LA_ODD ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs ->
  nk_n_if kbs = 60 + j ->
  aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs (lf_tab_at (60 + j)) ->
  lf_ifp (rdW W3 (ms_mem ms3)) (60 + j) ->
  (forall r, 0 <= r < NK_SIZE -> ~ (NK_IF_NAME <= r < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= r < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= r < NK_N_IF + 4) ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + r) 1 0) ->
  lf_gnames_at 64 (rdW W3 (ms_mem ms3)) ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) (OL_A6 j) q -> q <> 0 ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) q (nth (Z.to_nat (1 + j)) lf_odd_strs []) ->
  (forall i, 0 <= i <= Z.of_nat (length (nth (Z.to_nat (1 + j)) lf_odd_strs [])) ->
     in_roP SEGS PCAP_RLO PCAP_RHI (q + i)) ->
  kagree SEGS (ol_XX j) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + OL_IFNo j) 8 q ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + OL_IFIo j) 4 (101 + j) ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + NK_N_IF) 4 (61 + j) ->
  lf_shape fy pc ms4 -> lf_core cx ms4 ->
  getr (ms_regs ms4) 19 = getr (ms_regs ms3) 19 ->
  exists kbs', kbs' = abytes_of SEGS (rdW W3 (ms_mem ms4)) LA_G_NL (Z.to_nat NK_SIZE) /\
    lf_setup_inv B MT MS la_nul pc cx fy fp k2 ly3 S3 W3 ms4 md4 /\
    lf_slot cx W3 ms4 LS_ODD LA_ODD /\
    anlk_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs' /\
    nk_n_if kbs' = 61 + j /\
    aiftab_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs' (lf_tab_at (61 + j)) /\
    lf_ifp (rdW W3 (ms_mem ms4)) (61 + j) /\
    (forall r, 0 <= r < NK_SIZE -> ~ (NK_IF_NAME <= r < NK_IF_NAME + 640) ->
       ~ (NK_IF_INDEX <= r < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= r < NK_N_IF + 4) ->
       val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + r) 1 0) /\
    lf_gnames_at 64 (rdW W3 (ms_mem ms4)).
Proof.
  intros fy cx fp k2 ly3 S3 W3 ms3 ms4 md3 md4 j kbs q pc Hj HMS HLN HAR HFR Hce Hsp0 Hsp16 Hsp47 HPL
    HSETUP HSODD HNLK HNIF HIFT HIFP HZERO HGN HQ HQ0 HQS HQRO HK HGrow Hfd Hfs HSN HSI HSNIF
    HSHAPE4 HCORE4 H19.
  pose proof (ol_nums j Hj) as N.
  pose proof HSETUP as (_ & _ & HSAVED & HHDR & HFSH & H19o & HSHB & HFK & HF & HF0 & HWA & HB160 &
                        HB1A0 & HB2E0 & HB330 & HCUR & HJBK & HGW & HOD & HTX & HLA).
  assert (XR : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ ol_XX j a).
  { intros a Ha. pose proof (in_roP_low a Ha) as Hlow. unfold kLowMemEnd in Hlow.
    apply ol_XX_not; [lia|]. intros HX. exact (ol_gnl_not_ro a (ol_X_gnl j a Hj HX) Ha). }
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ ol_XX j a)
    by (intros a Ha; apply ol_XX_not; [unfold LA_G_NAMES, G_NAMES_SIZE in *; lia|];
        intros HX; pose proof (ol_X_gnl j a Hj HX);
        unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE in *; lia).
  assert (XL : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304 -> ~ ol_XX j a)
    by (intros a Ha; apply ol_XX_not; [unfold LA_LONG_ALIAS in *; lia|];
        intros HX; pose proof (ol_X_gnl j a Hj HX);
        unfold LA_LONG_ALIAS, LA_G_NL, NK_SIZE in *; lia).
  pose proof HJBK as (_ & _ & HFA & _).
  pose proof HJBK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINCL & _).
  assert (XF : forall a, lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/
                 lf_slots_fp cx a \/ lf_cur_fp cx a -> ~ ol_XX j a)
    by (intros a Ha; exact (ol_X_miss_frame cx fp ly3 S3 W3 (ms_mem ms3) md3 j a Hj HAR HFR
                              (HFA LF_CID fp) Hce Hsp0 Hsp16 Hsp47 Ha)).
  assert (XJ : forall a, lf_jbk_fp MS la_nul cx (c_T cx) a -> ~ ol_XX j a)
    by (intros a Ha; exact (ol_X_miss_jbk cx (c_T cx) ly3 S3 W3 (ms_mem ms3) md3 j a Hj HMS HLN HAR
                              HINCL HPL Ha)).
  set (kbs' := abytes_of SEGS (rdW W3 (ms_mem ms4)) LA_G_NL (Z.to_nat NK_SIZE)).
  assert (HNLK' : anlk_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs')
    by (unfold kbs'; exact (ol_nlk_after _ _ kbs HNLK HGrow)).
  assert (HNIF' : nk_n_if kbs' = 61 + j).
  { unfold nk_n_if, fld_u32, kbs'.
    exact (ol_fld_of_val _ NK_N_IF 4%nat (61 + j) ltac:(unfold NK_N_IF; lia)
             ltac:(unfold NK_N_IF, NK_SIZE; cbn [Z.of_nat]; lia)
             ltac:(cbn [Z.of_nat Z.mul]; lia) HSNIF). }
  assert (HZERO' : forall r, 0 <= r < NK_SIZE -> ~ (NK_IF_NAME <= r < NK_IF_NAME + 640) ->
            ~ (NK_IF_INDEX <= r < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= r < NK_N_IF + 4) ->
            val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + r) 1 0).
  { intros r Hr H1 H2 H3.
    apply (val_mem_keep SEGS (ol_XX j) _ _ (LA_G_NL + r) 1%nat 0 HK); [|exact (HZERO r Hr H1 H2 H3)].
    intros k Hk. cbn [Z.of_nat] in Hk.
    apply ol_XX_not; [unfold LA_G_NL, NK_SIZE in *; lia|]. intros HX.
    pose proof (ol_X_gnl j (LA_G_NL + r + k) Hj HX).
    unfold OL_X, OL_IFNo, OL_IFIo, NK_IF_NAME, NK_IF_INDEX, NK_N_IF, NK_SIZE in *. lia. }
  destruct (ol_tab_step _ _ j kbs kbs' q Hj HK HNLK HIFT HIFP HGN HOD HNIF' HSN HSI HQ HQ0 HQS HQRO)
    as (HIFT' & HIFP').
  exists kbs'. split; [reflexivity|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - split; [exact HSHAPE4|]. split; [exact HCORE4|].
    split; [exact (lf_saved_keep (ol_XX j) cx W3 ms3 W3 ms4 HK ltac:(intros a Ha; apply XF; left; exact Ha)
                     HSAVED)|].
    split; [exact (lf_header_keep (ol_XX j) cx fp W3 ms3 W3 ms4 HK
                     ltac:(intros a Ha; apply XF; right; left; exact Ha) HHDR)|].
    split; [apply (lf_fshadow_keep (ol_XX j) cx fp W3 ms3 W3 ms4 LF_SH0 HK); [|exact HFSH];
            intros a Ha; apply XF; right; right; left;
            unfold lf_fshadow_fp in *; rewrite LF_SH0_len in Ha; unfold LF_NSH in Ha;
            cbn [Z.of_nat] in Ha; exact Ha|].
    split; [rewrite H19; exact H19o|].
    pose proof (ol_slots_keep (ol_XX j) cx fp W3 ms3 W3 ms4 HK
                  ltac:(intros a Ha; apply XF; right; right; right; left; exact Ha)
                  (conj HSHB (conj HFK (conj HF (conj HF0 (conj HWA (conj HB160 (conj HB1A0
                    (conj HB2E0 (conj HB330 HSODD))))))))))
      as (HSHB' & HFK' & HF' & HF0' & HWA' & HB160' & HB1A0' & HB2E0' & HB330' & HSODD').
    split; [exact HSHB'|]. split; [exact HFK'|]. split; [exact HF'|]. split; [exact HF0'|].
    split; [exact HWA'|]. split; [exact HB160'|]. split; [exact HB1A0'|]. split; [exact HB2E0'|].
    split; [exact HB330'|].
    split; [apply (lf_cur_keep (ol_XX j) cx W3 ms3 W3 ms4 _ _ HK); [|exact HCUR];
            intros a Ha; apply XF; right; right; right; right; exact Ha|].
    split; [eapply lf_jbk_keep; [exact HK | exact Hfd | exact Hfs | exact XJ | exact HJBK]|].
    split; [eapply lf_gnames_w_keep; [exact HK | apply wcarry_of_grows; exact HGrow | exact XN | exact HGW]|].
    split; [eapply lf_odd_at_keep; [exact HK | exact XR | exact HOD]|].
    split; [eapply lf_texts_at_keep; [exact HK | exact XR | exact HTX]|].
    eapply lf_la_at_keep; [exact HK | apply wcarry_of_grows; exact HGrow | exact XL | exact HLA].
  - apply (lf_slot_keep (ol_XX j) cx W3 ms3 W3 ms4 LS_ODD LA_ODD HK); [|exact HSODD].
    intros i Hi. apply XF. right; right; right; left. unfold lf_slots_fp, LS_ODD in *. lia.
  - exact HNLK'.
  - exact HNIF'.
  - exact HIFT'.
  - exact HIFP'.
  - exact HZERO'.
  - eapply lf_gnames_at_keep; [exact HK | lia | exact XN | exact HGN].
Qed.

(* the state the back-edge test runs from: no memory, the two registers it compares *)
Lemma ol_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma ol_entry_br : forall (fy : YK11.FPState) j q0 (W3 : world SEGS) (ms4 : machine_state),
  0 <= j < 4 -> lf_shape fy OL_BR ms4 ->
  getr (ms_regs ms4) 5 = w64 (- 0x28) ->
  getr (ms_regs ms4) 11 = w64 (- 16 - 8 * j) ->
  getr (ms_regs ms4) 27 = w64 SHADOW_OFF ->
  @st_ok_pi SEGS pa_val fy (ol_E (ms_regs ms4) q0) (ol_ss_br j) (restrict (w_H W3) ms4).
Proof.
  intros fy j q0 W3 ms4 Hj HSH H5 H11 H27.
  set (E := ol_E (ms_regs ms4) q0) in *.
  assert (E27 : ew E 27 = w64 SHADOW_OFF)
    by (unfold E; rewrite (ol_E_reg _ q0 27%nat (27%bv : bv 5) eq_refl); exact H27).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
    by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  rewrite (ol_ms_shape fy OL_BR ms4 (w_H W3) HSH).
  assert (HS0 : @st_ok_pi SEGS pa_val fy E
    (mkSS OL_BR sr_atoms [] None (mkFacts [(27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
    (@YK11.mkst fy (ms_regs ms4) (w64 (BASE + OL_BR)) (mrestrict (w_H W3) (ms_mem ms4)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - unfold E, ol_E. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn [map extent_of_region zpairwise_disjoint]. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U27. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; lia. }
  pose proof (ol_set_lit fy E _ _ (5%bv : bv 5) (2 ^ 64 - 40) (- 0x28) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs YK11.mkst]; exact H5) ltac:(lia)) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  pose proof (ol_set_lit fy E _ _ (11%bv : bv 5) (2 ^ 64 - 16 - 8 * j) (- 16 - 8 * j) HS1
    ltac:(discriminate) ltac:(cbn [ms_regs YK11.mkst]; exact H11) ltac:(lia)) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  exact HS2.
Qed.

(* the cut at the head of turn j + 1, from the clauses the turn leaves *)
Lemma ol_inv_next : forall (fy : YK11.FPState) cx fp k2 ly3 S3 (W3 : world SEGS) (ms4 : machine_state) md4 j kbs',
  0 <= j < 3 ->
  lf_setup_inv B MT MS la_nul LF_ol cx fy fp k2 ly3 S3 W3 ms4 md4 ->
  lf_slot cx W3 ms4 LS_ODD LA_ODD ->
  anlk_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs' ->
  nk_n_if kbs' = 61 + j ->
  aiftab_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs' (lf_tab_at (61 + j)) ->
  lf_ifp (rdW W3 (ms_mem ms4)) (61 + j) ->
  (forall r, 0 <= r < NK_SIZE -> ~ (NK_IF_NAME <= r < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= r < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= r < NK_N_IF + 4) ->
     val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + r) 1 0) ->
  lf_gnames_at 64 (rdW W3 (ms_mem ms4)) ->
  getr (ms_regs ms4) 18 = w64 LA_G_NL ->
  getr (ms_regs ms4) 26 = w64 (lf_F cx fp + LO_WA) ->
  getr (ms_regs ms4) 27 = w64 SHADOW_OFF ->
  getr (ms_regs ms4) 11 = w64 (- 8 - 8 * (j + 1)) ->
  getr (ms_regs ms4) 12 = w64 (101 + (j + 1)) ->
  getr (ms_regs ms4) 13 = w64 (LA_G_NL + 0x42000) ->
  getr (ms_regs ms4) 14 = w64 (0x422b0) ->
  getr (ms_regs ms4) 15 = w64 (0x42530) ->
  getr (ms_regs ms4) 16 = w64 (LA_ODD + 8 + 8 * (j + 1)) ->
  getr (ms_regs ms4) 17 = w64 (SHADOW_OFF + (LA_ODD + 8 + 8 * (j + 1)) / 8) ->
  getr (ms_regs ms4) 5 = w64 (- 0x28) ->
  lf_ol_inv B MT MS la_nul (j + 1) cx fy fp k2 ly3 S3 W3 ms4 md4.
Proof.
  intros fy cx fp k2 ly3 S3 W3 ms4 md4 j kbs' Hj HSET HODD HNLK HN HT HP HZ HG
    R18 R26 R27 R11 R12 R13 R14 R15 R16 R17 R5.
  exists kbs'. split; [lia|]. split; [exact HSET|].
  split; [exact R18|]. split; [exact R26|]. split; [exact R27|]. split; [exact HODD|].
  split; [exact R11|]. split; [exact R12|]. split; [exact R13|]. split; [exact R14|].
  split; [exact R15|]. split; [exact R16|]. split; [exact R17|]. split; [exact R5|].
  split; [exact HNLK|].
  split; [rewrite (ol_tab_len (j + 1)) by lia; lia|].
  replace (60 + (j + 1)) with (61 + j) by lia.
  split; [exact HT|]. split; [exact HP|]. split; [exact HZ | exact HG].
Qed.

(* the cut at the two callocs, from the clauses the last turn leaves: the fields the set-up never wrote are
   still the zero bytes the entry left *)
Lemma ol_inv_ca : forall (fy : YK11.FPState) cx fp k2 ly3 S3 (W3 : world SEGS) (ms4 : machine_state) md4 kbs',
  kbs' = abytes_of SEGS (rdW W3 (ms_mem ms4)) LA_G_NL (Z.to_nat NK_SIZE) ->
  lf_setup_inv B MT MS la_nul LF_ca cx fy fp k2 ly3 S3 W3 ms4 md4 ->
  lf_slot cx W3 ms4 LS_ODD LA_ODD ->
  anlk_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs' ->
  nk_n_if kbs' = 64 ->
  aiftab_at SEGS (rdW W3 (ms_mem ms4)) LA_G_NL kbs' (lf_tab_at 64) ->
  lf_ifp (rdW W3 (ms_mem ms4)) 64 ->
  (forall r, 0 <= r < NK_SIZE -> ~ (NK_IF_NAME <= r < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= r < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= r < NK_N_IF + 4) ->
     val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + r) 1 0) ->
  lf_gnames_at 64 (rdW W3 (ms_mem ms4)) ->
  getr (ms_regs ms4) 18 = w64 LA_G_NL ->
  getr (ms_regs ms4) 26 = w64 (lf_F cx fp + LO_WA) ->
  getr (ms_regs ms4) 27 = w64 SHADOW_OFF ->
  lf_ca_inv B MT MS la_nul cx fy fp k2 ly3 S3 W3 ms4 md4.
Proof.
  intros fy cx fp k2 ly3 S3 W3 ms4 md4 kbs' Hkb HSET HODD HNLK HN HT HP HZ HG R18 R26 R27.
  assert (FZ : forall off, 0 <= off -> off + 4 <= NK_IF_NAME -> fld_u32 kbs' off = 0).
  { intros off H0 H1.
    assert (HV : val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + off) 4 0).
    { apply ol_zero4. intros r Hr. apply HZ; unfold NK_SIZE, NK_IF_NAME, NK_IF_INDEX, NK_N_IF in *; lia. }
    rewrite Hkb. unfold fld_u32.
    exact (ol_fld_of_val _ off 4%nat 0 H0 ltac:(unfold NK_SIZE, NK_IF_NAME in *; cbn [Z.of_nat]; lia)
             ltac:(cbn [Z.of_nat Z.mul]; lia) HV). }
  assert (Z1 : nk_n_chunks kbs' = 0) by (apply FZ; unfold NK_N_CHUNKS, NK_IF_NAME; lia).
  assert (Z2 : nk_next kbs' = 0) by (apply FZ; unfold NK_NEXT, NK_IF_NAME; lia).
  assert (Z3 : nk_end_errno kbs' = 0) by (apply FZ; unfold NK_END_ERRNO, NK_IF_NAME; lia).
  assert (Z4 : nk_socket_errno kbs' = 0) by (apply FZ; unfold NK_SOCKET_ERRNO, NK_IF_NAME; lia).
  assert (Z5 : nk_send_errno kbs' = 0) by (apply FZ; unfold NK_SEND_ERRNO, NK_IF_NAME; lia).
  assert (Z6 : nk_open kbs' = 0) by (apply FZ; unfold NK_OPEN, NK_IF_NAME; lia).
  assert (Z7 : nk_opened kbs' = 0) by (apply FZ; unfold NK_OPENED, NK_IF_NAME; lia).
  assert (Z8 : nk_closed kbs' = 0) by (apply FZ; unfold NK_CLOSED, NK_IF_NAME; lia).
  assert (Z9 : nk_misuse kbs' = 0) by (apply FZ; unfold NK_MISUSE, NK_IF_NAME; lia).
  assert (Z10 : nk_n_sent kbs' = 0) by (apply FZ; unfold NK_N_SENT, NK_IF_NAME; lia).
  exists kbs'. split; [exact HSET|].
  split; [exact R18|]. split; [exact R26|]. split; [exact R27|]. split; [exact HODD|].
  split; [exact HNLK|].
  split.
  { unfold nlk_wf. rewrite Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, HN.
    unfold NL_CHUNKS, NL_SENT_MAX. repeat split; try lia; intros i Hi; lia. }
  split; [exact Z6|]. split; [exact Z9|]. split; [rewrite Z7, Z8; reflexivity|].
  split; [exact HN|]. split; [rewrite <- lf_tab_full; exact HT|]. split; [exact HP|].
  split; [exact Z1|]. split; [exact Z10|]. split; [exact Z2|]. split; [exact Z7 | exact HG].
Qed.

Lemma ol_XX_range : forall j a, ~ ol_XX j a -> 0 <= a < 2 ^ 64.
Proof.
  intros j a H. destruct (Z.le_gt_cases 0 a) as [H0 | H0]; [|exfalso; apply H; left; lia].
  destruct (Z.lt_ge_cases a (2 ^ 64)) as [H1 | H1]; [lia | exfalso; apply H; left; lia].
Qed.

(* ---- the tactics of a turn's continuation ---- *)
(* the run's writable windows lie in ol_XX: three of g_nl's words; the odd entry's window is empty *)
Ltac ol_u18 Ex HU :=
  let U18 := ident:(U18) in
  assert (HU : bv_unsigned (ew Ex 18) = LA_G_NL) by (cbn [ew ewset extK Nat.eqb]; exact U18).
Ltac ol_win Ex :=
  let HU := fresh "HU" in ol_u18 Ex HU;
  let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hr := fresh "Hr" in
  let Hrr := fresh "Hrr" in
  intros a Ha (r & Hr & Hrr); vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr];
          [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hrr;
            rewrite ?HU in Hrr; right;
            unfold OL_X, OL_IFNo, OL_IFIo, NK_N_IF, NK_IF_NAME, NK_IF_INDEX in *; lia
          | ]);
  destruct Hr.
(* fold a run's frame and growth into the agreement (KW) and the growth (GW) since the cut *)
Ltac ol_acc :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2),
    KW : kagree _ ?X ?m0 (mrestrict ?H ?m1),
    HGq : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2),
    GW : mem_grows ?m0 (mrestrict ?H ?m1) |- _ =>
      let K := fresh "KW" in
      pose proof (ol_kagree_step _ E rs _ _ _ X KW HFr
        ltac:(let a := fresh "a" in intros a; exact (ol_XX_range _ a)) ltac:(ol_win E)) as K;
      let G := fresh "GW" in
      pose proof ((fun x Hx => HGq x (GW x Hx)) : mem_grows m0 (mrestrict H m2)) as G;
      clear KW GW HFr HGq; rename K into KW; rename G into GW
  end.
(* the run's writable windows are g_nl's bytes, a range of G *)
Ltac ol_awr :=
  let HS := ident:(HS) in
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  let HU := fresh "HU" in ol_u18 Ex HU;
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
          [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha;
            rewrite ?HU in Ha;
            first [ lia
                  | right; left; apply (inG_of_In G_HARNESS LA_G_NL 271992 a);
                    [ cbn [G_HARNESS In]; left; reflexivity
                    | unfold OL_IFNo, OL_IFIo, NK_N_IF, NK_IF_NAME, NK_IF_INDEX in *; lia ] ]
          | ]);
  destruct Hin end.

(* a register of the state the runs leave: its symbolic value *)
Ltac ol_reg r :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
    rewrite (st_ok_pi_restrict_reg _ Ex ss msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e
  end.
Ltac ol_atom Ev := rewrite ol_den_atom; cbn [ew ewset extK Nat.eqb]; exact Ev.
Ltac ol_lit := rewrite ol_den_lit; try unfold w64; apply Z_to_bv64_eq_mod; vm_compute; reflexivity.
Ltac ol_num := unfold LA_G_NL, OL_A6, LA_ODD, SHADOW_OFF in *; lia.
Ltac ol_off Ev :=
  lazymatch type of Ev with _ = w64 ?v =>
  lazymatch goal with |- sv_denot ?Ex (SOff ?n ?c) = _ =>
    rewrite (lf_sv_off Ex n v c ltac:(cbn [ew ewset extK Nat.eqb]; exact Ev) ltac:(ol_num) ltac:(ol_num));
    unfold w64; apply Z_to_bv64_eq_mod; vm_compute; reflexivity
  end end.

(* ==========================================================================
   7. One turn of the loop
   ========================================================================== *)

#[local] Notation FROM POST GI :=
  (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Notation OL j := (lf_ol_inv B MT MS la_nul j).
#[local] Notation CA := (lf_ca_inv B MT MS la_nul).

Lemma lf_ol : forall POST, FROM POST CA -> forall j, 0 <= j < 4 -> FROM POST (OL j).
Proof.
  intros POST HCA.
  assert (TURN : forall j, 0 <= j < 4 -> (j < 3 -> FROM POST (OL (j + 1))) -> FROM POST (OL j)).
  { intros j Hj HNEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HBASE HFXR HJ3 HFR HINV.
    pose proof (ol_nums j Hj) as N.
    pose proof HBASE as (HPRE & HFZ & HGX & HLN & HMS & HE0 & HE0sp & HCTXs & HMO1 & HMO2 & HMO3 & HBUD &
                         HXMN & HMTL & HMTF).
    destruct HINV as (kbs & Hj' & HSETUP & H18 & H26 & H27 & HODD & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
                      H5 & HNLK & HNIF & HIFT & HIFP & HZERO & HGN).
    pose proof HSETUP as (HSHAPE & HCORE & HSAVED & HHDR & HFSH & H19 & HSHB & HFK & HF & HF0 & HWA & HB160 &
                          HB1A0 & HB2E0 & HB330 & HCUR & HJBK & HGW & HOD & HTX & HLA).
    (* the odd entry this turn copies *)
    destruct (HOD (Z.to_nat (1 + j)) ltac:(lia)) as (q & HQ & HQ0 & HQS & HQRO).
    replace (LA_ODD + 8 * Z.of_nat (Z.to_nat (1 + j))) with (OL_A6 j) in HQ
      by (unfold OL_A6; lia).
    assert (Hqr : 0 <= q < 2 ^ 64).
    { pose proof HQS as ((Hq0 & Hq1 & _) & _). rewrite length_app in Hq1. cbn [length] in Hq1. lia. }
    (* the number of entries so far *)
    assert (HNIFz : nk_n_if kbs = 60 + j) by (rewrite HNIF; apply ol_tab_len; lia).
    (* the journal's allocator state *)
    pose proof HJ3 as (HSTKb & HXOb & (memS & HJi & _) & _).
    pose proof (proj1 HJi) as HAR.
    (* the shadow of the two objects the turn checks *)
    assert (HRAO : range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF (OL_A6 j) 8).
    { destruct (lf_zsh_odd_rd B TB ly3 S3 (ard SEGS (rdW W3 (ms_mem ms3))) (proj1 HAR)) as (HR & _).
      apply (lf_ra_sub _ LA_ODD 48 _ _ HR); unfold OL_A6, LA_ODD in *; lia. }
    assert (HRAG : forall p n, LA_G_NL <= p -> p + n <= LA_G_NL + NK_SIZE ->
              range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF p n).
    { intros p n Hp Hn. destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem ms3) md3 HAR) as (HR & _).
      apply (lf_ra_sub _ LA_G_NL NK_SIZE _ _ HR); lia. }
    (* the entry state *)
    set (E := ol_E (ms_regs ms3) q) in *.
    assert (HEI : img_env pa_val A_LIM E) by (unfold E; apply ol_E_img).
    assert (HS : @st_ok_pi SEGS pa_val fy E (ol_ss j) (restrict (w_H W3) ms3))
      by (unfold E; exact (ol_entry fy j q kbs W3 ms3 Hj Hqr HSHAPE H5 H11 H12 H13 H14 H15 H16 H17 H18 H27
                             HNLK HNIFz HQ)).
    assert (SHOK : sh_ok SEGS OL_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
    assert (E18 : ew E 18 = w64 LA_G_NL)
      by (unfold E, ol_E; rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 18%nat (18%bv : bv 5) eq_refl); exact H18).
    assert (E27 : ew E 27 = w64 SHADOW_OFF)
      by (unfold E, ol_E; rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 27%nat (27%bv : bv 5) eq_refl); exact H27).
    assert (E16 : ew E 16 = w64 (OL_A6 j))
      by (unfold E, ol_E; rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 16%nat (16%bv : bv 5) eq_refl); exact H16).
    assert (U18 : bv_unsigned (ew E 18) = LA_G_NL)
      by (rewrite E18; apply unsigned_lit_small; unfold LA_G_NL; lia).
    assert (UB : U E OL_BX = SHADOW_OFF)
      by (unfold OL_BX; rewrite (U_atom_off E 27%nat SHADOW_OFF 0 E27 ltac:(unfold SHADOW_OFF; lia)
            ltac:(unfold SHADOW_OFF; lia)); lia).
    assert (UA6 : U E (SOff 16 0) = OL_A6 j)
      by (rewrite (U_atom_off E 16%nat (OL_A6 j) 0 E16 ltac:(unfold OL_A6, LA_ODD in *; lia)
            ltac:(unfold OL_A6, LA_ODD in *; lia)); lia).
    assert (UG : forall c, 0 <= c <= NK_SIZE -> U E (SOff 18 c) = LA_G_NL + c)
      by (intros c Hc; rewrite (U_atom_off E 18%nat LA_G_NL c E18 ltac:(unfold LA_G_NL; lia)
            ltac:(unfold LA_G_NL, NK_SIZE in *; lia)); lia).
    (* what the continuation reads off the cut: the registers the turn leaves, in E *)
    pose proof HCORE as (C2 & C8 & C9 & C3 & C4).
    assert (EA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
      by (intros n r Hn; unfold E; exact (ol_E_reg _ q n r Hn)).
    assert (E02 : ew E 2 = w64 (lf_sp1 cx)) by (rewrite (EA 2%nat 2%bv eq_refl); exact C2).
    assert (E08 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (EA 8%nat 8%bv eq_refl); exact C8).
    assert (E09 : ew E 9 = w64 (lf_sp1 cx)) by (rewrite (EA 9%nat 9%bv eq_refl); exact C9).
    assert (E03 : ew E 3 = getr (c_regs cx) 3) by (rewrite (EA 3%nat 3%bv eq_refl); exact C3).
    assert (E04 : ew E 4 = getr (c_regs cx) 4) by (rewrite (EA 4%nat 4%bv eq_refl); exact C4).
    assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by exact (EA 19%nat 19%bv eq_refl).
    assert (E26 : ew E 26 = w64 (lf_F cx fp + LO_WA)) by (rewrite (EA 26%nat 26%bv eq_refl); exact H26).
    assert (E32 : ew E 32 = Z_to_bv 64 q) by (unfold E; exact (ol_E_q _ q)).
    clear EA. clearbody E.
    (* the journal's stack and the payload block *)
    pose proof asan_consts as ((C1a & C1b) & C2' & C3' & C4' & C5').
    pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkJ & _).
    destruct HstkJ as (Hsp0al & _ & HceilJ & HsloJ & HshiJ & H47J & _).
    rewrite !Z.add_0_r in Hsp0al, HsloJ, HshiJ.
    assert (Hce : alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK) by lia.
    assert (Hsp0 : 0 <= spZ (c_regs cx) - LF_MFRAME) by (unfold LF_MFRAME, LLVMF_STK, ESTACK in *; lia).
    assert (Hsp47 : spZ (c_regs cx) <= 2 ^ 47) by lia.
    assert (HFIN : In (LF_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
    assert (HPL : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { intros Hn. pose proof HPRE as (_ & _ & _ & _ & HPB & _).
      destruct HPB as [(Hn0 & _) | (_ & Hb)]; [lia|].
      pose proof HJBK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (D & _ & HPm) & _).
      apply (Permutation_in _ (Permutation_sym HPm)).
      apply in_or_app. right. apply in_or_app. right. exact Hb. }
    assert (KW : kagree SEGS (ol_XX j) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms3))) by apply kagree_refl.
    assert (GW : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms3))) by (intros x Hx; exact Hx).
    pose proof (paj_run_to_x (fx := fy) SK B LAWS G_HARNESS HGX 0 (@nil (Z * Z))) as RUNTO.
    (* the four turns, each at its own numbers: +0x408 .. +0x47c *)
    assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj4 as [ -> | [ -> | [ -> | -> ] ] ];
      paj_run_to_tok RUNTO HS HJ3 SHOK Bspan OL_BR;
      try solve
      [ rewrite UB, UG by (unfold NK_SIZE; lia); apply HRAG; unfold NK_SIZE; lia
      | rewrite UB, UA6; exact HRAO ].
    all: lazymatch goal with |- awr_ok_x _ _ _ _ _ _ _ _ _ _ _ _ => ol_awr | _ => ol_acc end.
    (* the back edge: to +0x494 for the last turn, to +0x408 for the first three *)
    4: paj_run_to_tok RUNTO HS HJ3 SHOK Bspan LF_ca.
    1-3: paj_run_to_tok RUNTO HS HJ3 SHOK Bspan LF_ol.
    all: lazymatch goal with |- awr_ok_x _ _ _ _ _ _ _ _ _ _ _ _ => ol_awr | _ => ol_acc end.
    (* the clauses of the cut the turn reaches *)
    all: lazymatch type of HNIFz with _ = 60 + ?jj =>
         lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      assert (FDF : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
        by (rewrite ?lf_wvb_fds, ?lf_wvb_fs; split; reflexivity);
      assert (VN : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + NK_N_IF) 4 (61 + jj))
        by (spregion HS 1%nat HR1;
            eapply (field_of_region (segs := SEGS) _ _ 18%nat LA_G_NL _ _ _ _ _ _ 4%N);
            [ exact HR1 | cbn [ew ewset extK Nat.eqb]; exact U18 | cbn [In]; left; reflexivity
            | ol_lit | cbn; lia | cbn; lia ]);
      assert (VNM : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + OL_IFNo jj) 8 q)
        by (spregion HS 2%nat HR2;
            eapply (field_of_region (segs := SEGS) _ _ 18%nat LA_G_NL _ _ _ _ _ _ 8%N);
            [ exact HR2 | cbn [ew ewset extK Nat.eqb]; exact U18 | cbn [In]; left; reflexivity
            | ol_atom E32 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hqr | cbn; lia ]);
      assert (VIX : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + OL_IFIo jj) 4 (101 + jj))
        by (spregion HS 3%nat HR3;
            eapply (field_of_region (segs := SEGS) _ _ 18%nat LA_G_NL _ _ _ _ _ _ 4%N);
            [ exact HR3 | cbn [ew ewset extK Nat.eqb]; exact U18 | cbn [In]; left; reflexivity
            | ol_lit | cbn; lia | cbn; lia ]);
      pose proof (lf_shape_of_st_ok fy W3 _ _ _ HS eq_refl) as SH4; cbn [ss_pc] in SH4;
      assert (CO4 : lf_core cx msF)
        by (split; [ol_reg (2%bv : bv 5); ol_atom E02 | split; [ol_reg (8%bv : bv 5); ol_atom E08 |
            split; [ol_reg (9%bv : bv 5); ol_atom E09 | split; [ol_reg (3%bv : bv 5); ol_atom E03 |
            ol_reg (4%bv : bv 5); ol_atom E04]]]]);
      assert (R19 : getr (ms_regs msF) 19 = getr (ms_regs ms3) 19)
        by (ol_reg (19%bv : bv 5); ol_atom E19);
      assert (R18 : getr (ms_regs msF) 18 = w64 LA_G_NL) by (ol_reg (18%bv : bv 5); ol_atom E18);
      assert (R26 : getr (ms_regs msF) 26 = w64 (lf_F cx fp + LO_WA)) by (ol_reg (26%bv : bv 5); ol_atom E26);
      assert (R27 : getr (ms_regs msF) 27 = w64 SHADOW_OFF) by (ol_reg (27%bv : bv 5); ol_atom E27);
      destruct (ol_core_next fy cx fp k2 ly3 S3 W3 ms3 msF md3 mdF jj kbs q _ Hj HMS HLN HAR HFIN Hce Hsp0
        Hsp0al Hsp47 HPL HSETUP HODD HNLK HNIFz HIFT HIFP HZERO HGN HQ HQ0 HQS HQRO KW GW
        (proj1 FDF) (proj2 FDF) VNM VIX VN SH4 CO4 R19)
        as (kbs' & Hkb & HSET' & HODD' & HNLK' & HNIF' & HIFT' & HIFP' & HZERO' & HGN')
    end end.
    (* turns 0, 1, 2: the head of the next turn *)
    1-3: apply (HNEXT ltac:(lia) cx fy fp k2 ly3 S3 W3 _ _ HBASE HFXR HJ3 HFR);
      eapply ol_inv_next; [lia | exact HSET' | exact HODD' | exact HNLK' | exact HNIF' | exact HIFT'
        | exact HIFP' | exact HZERO' | exact HGN' | exact R18 | exact R26 | exact R27
        | ol_reg (11%bv : bv 5); ol_lit | ol_reg (12%bv : bv 5); ol_lit
        | ol_reg (13%bv : bv 5); ol_off E18 | ol_reg (14%bv : bv 5); ol_lit
        | ol_reg (15%bv : bv 5); ol_lit | ol_reg (16%bv : bv 5); ol_off E16
        | ol_reg (17%bv : bv 5);
          lazymatch type of E16 with _ = w64 ?v =>
          lazymatch goal with |- sv_denot ?Ex _ = _ =>
            etransitivity;
            [ exact (ol_den_a7 Ex v SHADOW_OFF ltac:(cbn [ew ewset extK Nat.eqb]; exact E16)
                ltac:(ol_num) ltac:(cbn [ew ewset extK Nat.eqb]; exact E27) ltac:(ol_num) ltac:(ol_num))
            | unfold w64; apply Z_to_bv64_eq_mod; vm_compute; reflexivity ] end end
        | ol_reg (5%bv : bv 5); ol_lit ].
    (* turn 3: the two callocs *)
    apply (HCA cx fy fp k2 ly3 S3 W3 _ _ HBASE HFXR HJ3 HFR).
    eapply ol_inv_ca; [exact Hkb | exact HSET' | exact HODD' | exact HNLK' | exact HNIF'
      | exact HIFT' | exact HIFP' | exact HZERO' | exact HGN' | exact R18 | exact R26 | exact R27]. }
  assert (M : forall n j, 0 <= j < 4 -> 4 - j <= Z.of_nat n -> FROM POST (OL j)).
  { induction n as [|n IH]; intros j Hj Hn; [cbn in Hn; lia|].
    apply (TURN j Hj). intros Hlt. apply IH; [lia|]. rewrite Nat2Z.inj_succ in Hn. lia. }
  intros j Hj. apply (M (Z.to_nat (4 - j)) j Hj). rewrite Z2Nat.id by lia. lia.
Qed.

End b.
End a.
