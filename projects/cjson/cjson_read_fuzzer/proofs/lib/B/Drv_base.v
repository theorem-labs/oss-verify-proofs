(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface CJ_tree AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RSN : nat := 65536.
Arguments RSN : simpl never.
Lemma RSN_Z : Z.of_nat RSN = 65536.
Proof. reflexivity. Qed.
#[global] Opaque RSN.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMAIN     : Z := 0x81ee4.   (* [comment removed for export] *)
Definition ATRUN     : Z := 0x821b4.   (* [comment removed for export] *)
Definition AEMIT     : Z := 0x8233c.   (* [comment removed for export] *)
Definition AFUZZE    : Z := 0x82384.   (* [comment removed for export] *)
Definition ATALLOC_INIT  : Z := 0x821a8.   (* [comment removed for export] *)
Definition ATALLOC_COUNT : Z := 0x821ac.   (* [comment removed for export] *)
Definition AEXITF    : Z := 0x8d998.   (* [comment removed for export] *)
Definition AOPEN     : Z := 0x8dc0c.   (* [comment removed for export] *)
Definition ACLOSE    : Z := 0x9fff4.   (* [comment removed for export] *)
Definition AMREAD    : Z := 0xa00d4.   (* [comment removed for export] *)
Definition AREAD_T   : Z := 0x4251c.    (* [comment removed for export] *)
Definition AREAD_ICPT : Z := 0x4474c.
Definition AFWRITE_T : Z := 0x42520.    (* [comment removed for export] *)
Definition AFWRITE_ICPT : Z := 0x449bc.
Definition AMFWRITE  : Z := 0x93b5c.   (* [comment removed for export] *)
Definition AFPRINTF_T : Z := 0x42540.   (* [comment removed for export] *)
Definition AFPRINTF_ICPT : Z := 0x4722c.
Definition AVPRINTF_T : Z := 0x42534.   (* [comment removed for export] *)
Definition AVPRINTF_ICPT : Z := 0x4601c.
Definition AMVPRINTF  : Z := 0x9a0c8.  (* [comment removed for export] *)
Definition AVFPRINTF_T : Z := 0x42538.  (* [comment removed for export] *)
Definition AVFPRINTF_ICPT : Z := 0x46b80.
Definition AMVFPRINTF : Z := 0x93de4.  (* [comment removed for export] *)
Definition APRINTF_COMMON : Z := 0x460b8.
Definition ASTAGE2_RET : Z := 0x8d298.   (* [comment removed for export] *)
Definition AINITFLAG : Z := 0x5dc010.     (* [comment removed for export] *)
Definition AEMPTYBUF : Z := 0x5dc020.     (* [comment removed for export] *)
Definition AAEF_ARGC : Z := 0xa5c98.     (* [comment removed for export] *)
Definition AGOT_STDERR : Z := 0xa2360.   (* [comment removed for export] *)
Definition ASTDERR_VAR : Z := 0xa15f8.   (* [comment removed for export] *)
Definition AGOT_FUZZINIT : Z := 0xa2368. (* [comment removed for export] *)
Definition ATIDCELL  : Z := 0x5dc8c8.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_FMT_usage       : Z := 0x158dc.  (* [comment removed for export] *)
Definition A_FMT_cannot_open : Z := 0x1d79f.  (* [comment removed for export] *)
Definition A_FMT_read_error  : Z := 0x1d7b4.  (* [comment removed for export] *)
Definition A_FMT_too_big     : Z := 0x1976e.  (* [comment removed for export] *)
Definition A_FMT_dn          : Z := 0x1486b.  (* [comment removed for export] *)
Definition A_MSG_oom     : Z := 0x14857.  (* [comment removed for export] *)
Definition A_MSG_short   : Z := 0x1f8fb.  (* [comment removed for export] *)
Definition A_MSG_overrun : Z := 0x158ed.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARS : Z := 0x5cc010.
Lemma ARS_eq : ARS = 0x5cc010.   (* [comment removed for export] *)
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mframe (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) : list cell :=
  [CB 8 fj; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra0].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ADSTAT (tid : word) (m : word -> option byte) : Prop :=
  rw_cells bsegs m ATIDCELL [C4 tid]                                                  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5fcbe0 [C4 (wz 0)]                                            (* [comment removed for export] *)
  /\ (exists cdt thr sec : byte, exists tm1 : word,
        rw_cells bsegs m 0x5fcc00 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])   (* [comment removed for export] *)
  /\ ATEX m                                            (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5fcae0 [C8 (wz 0x71944)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa23b8 [C8 (wz 0xa1138); C8 (wz 0xa1128)]                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa1128 [C8 (wz 0x86dd4); C8 (wz 0x30d98)]                    (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa6350 [C1 (Z_to_bv 8 0)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa16d0 [C8 (wz 0x8d87c); C8 (wz 0)]                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa3400 [C8 (wz 0xa3400)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa2378 [C8 (wz 0xa6020); C8 (wz 0xa62e0)]                   (* [comment removed for export] *)
  /\ rw_cells bsegs m AOFL_HEAD [C8 (wz 0)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m ASTDIN_USED [C8 (wz ASTDIN)]
  /\ rw_cells bsegs m ASTDOUT_USED [C8 (wz ASTDOUT)]
  /\ rw_cells bsegs m ASTDERR_USED [C8 (wz ASTDERR)]
  /\ rw_cells bsegs m AGOT_STDERR [C8 (wz ASTDERR_VAR); C8 (wz 0)]                     (* [comment removed for export] *)
  /\ rw_cells bsegs m ASTDERR_VAR [C8 (wz ASTDERR)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m AGOT_GUARD [C8 (wz AGUARD)]
  /\ (exists canary : word, rw_cells bsegs m AGUARD [C8 canary]).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition adstat_addr (a : Z) : Prop :=
  (ATIDCELL <= a < ATIDCELL + 4) \/ (0x5fcbe0 <= a < 0x5fcbe4) \/ (0x5fcc00 <= a < 0x5fcc08)
  \/ atex_addr a \/ (0x5fcae0 <= a < 0x5fcae8)
  \/ (0xa23b8 <= a < 0xa23c8) \/ (0xa1128 <= a < 0xa1138)
  \/ (0xa6350 <= a < 0xa6351) \/ (0xa16d0 <= a < 0xa16e0) \/ (0xa3400 <= a < 0xa3408)
  \/ (0xa2378 <= a < 0xa2388) \/ (AOFL_HEAD <= a < AOFL_HEAD + 8) \/ (ASTDIN_USED <= a < ASTDIN_USED + 8)
  \/ (ASTDOUT_USED <= a < ASTDOUT_USED + 8) \/ (ASTDERR_USED <= a < ASTDERR_USED + 8)
  \/ (AGOT_STDERR <= a < AGOT_STDERR + 16) \/ (ASTDERR_VAR <= a < ASTDERR_VAR + 8)
  \/ (AGOT_GUARD <= a < AGOT_GUARD + 8) \/ (AGUARD <= a < AGUARD + 8).

(* [comment removed for export] *)
Lemma ATEX_magree : forall m m' (P : Z -> Prop),
  ATEX m -> magree P m m' -> (forall a, atex_addr a -> P a) -> ATEX m'.
Proof.
  intros m m' P AT AG HP.
  assert (TR : forall a cs, rw_cells bsegs m a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> atex_addr x) -> rw_cells bsegs m' a cs).
  { intros a cs H Ha. eapply rw_cells_magree; [exact AG| exact H|]. intros x Hx. apply HP. apply Ha. exact Hx. }
  unfold ATEX, ATEX1, ATEX2, atex_cells in *. cbn [app] in *.
  destruct AT as [((f1 & f2 & f3 & pad & j1 & H) & (j2 & G) & C)|((f1 & f2 & f3 & pad & H) & G & I & C)].
  - left. split; [exists f1, f2, f3, pad, j1; apply (TR _ _ H)| split; [exists j2; apply (TR _ _ G)| apply (TR _ _ C)]];
      unfold atex_addr, A_ATEXIT, A_AEF_INIT, AINCB; cbn; intros; lia.
  - right. split; [exists f1, f2, f3, pad; apply (TR _ _ H)| split; [apply (TR _ _ G)| split; [apply (TR _ _ I)| apply (TR _ _ C)]]];
      unfold atex_addr, A_ATEXIT, A_AEF_INIT, AINCB; cbn; intros; lia.
Qed.

Lemma ATEX_munch : forall W m m', ATEX m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv -> ~ atex_addr a) W -> ATEX m'.
Proof.
  intros W m m' AT MU WM FW.
  assert (OUT : forall a, atex_addr a -> outside W a).
  { clear MU. intros a Ha. induction FW as [|[lo hi] W Hx FW IH]; cbn; [exact I|]. split; [| exact IH]. intros R. exact (Hx a R Ha). }
  eapply (ATEX_magree m m' atex_addr); [exact AT| | intros a Ha; exact Ha].
  eapply magree_of_munch; [exact MU| exact WM|]. intros a _ Ha. exact (OUT a Ha).
Qed.

Ltac adstat_lits := unfold A_ATEXIT, A_AEF_INIT, AINCB, AINITFLAG, ATIDCELL, AOFL_HEAD, ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED, AGOT_STDERR, ASTDERR_VAR, AGOT_GUARD, AGUARD, ATP in *.

Lemma ADSTAT_magree : forall tid m m', ADSTAT tid m -> magree adstat_addr m m' -> ADSTAT tid m'.
Proof.
  intros tid m m' D AG. unfold ADSTAT in *.
  destruct D as (D1 & D2 & (cdt & thr & sec & tm1 & D3) & D4 & D6 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & (canary & D21)).
  Ltac tr AG := eapply rw_cells_magree; [exact AG| eassumption| unfold adstat_addr, atex_addr; adstat_lits; cbn; intros; lia].
  split; [tr AG|]. split; [tr AG|]. split; [exists cdt, thr, sec, tm1; tr AG|]. split; [eapply ATEX_magree; [exact D4| exact AG| intros a Ha; unfold adstat_addr; tauto]|].
  repeat match goal with |- _ /\ _ => split end; try (exists canary); tr AG.
Qed.

(* [comment removed for export] *)
Definition adstat_safe (iv : Z * Z) : Prop :=
  forall a, fst iv <= a < snd iv -> ~ adstat_addr a.

Lemma outside_of_Forall : forall (P : Z * Z -> Prop) W x,
  Forall P W -> (forall lo hi, P (lo, hi) -> ~ (lo <= x < hi)) -> outside W x.
Proof.
  intros P W x FW HP. induction FW as [|[lo hi] W Hx FW IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

Lemma ADSTAT_munch : forall tid W m m', ADSTAT tid m -> munch W m m' -> wmono bsegs m m' -> Forall adstat_safe W -> ADSTAT tid m'.
Proof.
  intros tid W m m' D MU WM FW. eapply ADSTAT_magree; [exact D|].
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha Hd.
  eapply outside_of_Forall; [exact FW|]. intros lo hi Hx Hin. exact (Hx a Hin Hd).
Qed.

(* [comment removed for export] *)
Definition adstat_easy (iv : Z * Z) : Prop :=
  snd iv <= fst iv \/ AIMG_HI <= fst iv
  \/ (ASTDERR <= fst iv /\ snd iv <= ASTDERR + 232) \/ (ASTDOUT <= fst iv /\ snd iv <= ASTDOUT + 232)
  \/ (ASTDOUT_BUF <= fst iv /\ snd iv <= ASTDOUT_BUF + 1032) \/ (AERRNO <= fst iv /\ snd iv <= AERRNO + 4)
  \/ (AINITFLAG + 16 <= fst iv /\ snd iv <= AINITFLAG + 32)          (* [comment removed for export] *)
  \/ (ARS <= fst iv /\ snd iv <= ARS + 65536).

Lemma adstat_easy_safe : forall iv, adstat_easy iv -> adstat_safe iv.
Proof.
  intros [lo hi] H a Ha Hd. cbn [fst snd] in *.
  unfold adstat_easy, adstat_addr, atex_addr, A_ATEXIT, A_AEF_INIT, AINCB, AIMG_HI, ASTDERR, ASTDOUT, ASTDOUT_BUF, AERRNO, AINITFLAG, ARS, ATIDCELL, AOFL_HEAD,
    ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED, AGOT_STDERR, ASTDERR_VAR, AGOT_GUARD, AGUARD, ATP in *. cbn [fst snd] in H. lia.
Qed.

Lemma ADSTAT_munch_easy : forall tid W m m', ADSTAT tid m -> munch W m m' -> wmono bsegs m m' -> Forall adstat_easy W -> ADSTAT tid m'.
Proof.
  intros tid W m m' D MU WM FW. eapply ADSTAT_munch; eauto. eapply Forall_impl; [| exact FW]. intros iv; apply adstat_easy_safe.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FDS0 : list (word * FdEntry) :=
  [(wz 0, FdChannel (wz 0)); (wz 1, FdChannel (wz 1)); (wz 2, FdChannel (wz 2))].
Definition FDS3 (e : FdEntry) : list (word * FdEntry) :=
  [(wz 3, e); (wz 0, FdChannel (wz 0)); (wz 1, FdChannel (wz 1)); (wz 2, FdChannel (wz 2))].

Lemma FDS0_alloc : alloc_fd FDS0 = wz 3. Proof. reflexivity. Qed.
Lemma FDS0_3 : fd_lookup FDS0 (wz 3) = None. Proof. reflexivity. Qed.
Lemma FDS0_insert : forall e, fd_insert FDS0 (alloc_fd FDS0) e = FDS3 e. Proof. reflexivity. Qed.
Lemma FDS3_insert : forall e e', fd_insert (FDS3 e) (wz 3) e' = FDS3 e'. Proof. reflexivity. Qed.
Lemma FDS3_remove : forall e, fd_remove (FDS3 e) (wz 3) = FDS0. Proof. reflexivity. Qed.
Lemma FDS3_3 : forall e, fd_lookup (FDS3 e) (wz 3) = Some e. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition chan_ok (mo : Model) (fd : Z) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).

(* [comment removed for export] *)
Record DMOD (fs : Fs) (F : list (word * FdEntry)) (mo : Model) : Prop := mkDMOD {
  dm_fds : m_fds mo = F; dm_fs : m_fs mo = fs; dm_halt : m_halted mo = None }.

Lemma DMOD_chan : forall fs F mo, DMOD fs F mo -> (F = FDS0 \/ exists e, F = FDS3 e) -> chan_ok mo 1 /\ chan_ok mo 2.
Proof.
  intros fs F mo [HF _ _] H. unfold chan_ok. rewrite HF. destruct H as [-> | [e ->]]; split; reflexivity.
Qed.

Lemma DMOD_with_fds : forall fs F F' mo, DMOD fs F mo -> DMOD fs F' (with_fds F' mo).
Proof. intros fs F F' mo [HF HS HH]. split; [reflexivity| exact HS| exact HH]. Qed.

(* [comment removed for export] *)
Lemma with_fds_vm : forall F mo,
  m_vmmaps (with_fds F mo) = m_vmmaps mo /\ m_vm_lazy (with_fds F mo) = m_vm_lazy mo /\ m_halted (with_fds F mo) = m_halted mo.
Proof. intros; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma disjoint_from_Forall : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof. intros P W a n FW HP. induction FW as [|[lo hi] W Hx FW IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH]. Qed.

Lemma stdout_file_munch : forall m m' so W,
  stdout_file m so -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => (snd iv <= ASTDOUT \/ ASTDOUT + 232 <= fst iv) /\ (snd iv <= ASTDOUT_BUF \/ ASTDOUT_BUF + 1024 <= fst iv)) W ->
  stdout_file m' so.
Proof.
  intros m m' so W (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM FW.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn; intros lo hi [H _]; lia.
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn; intros lo hi [_ H]; lia.
Qed.

Lemma stderr_wfile_munch : forall m m' W,
  stderr_wfile m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => snd iv <= ASTDERR \/ ASTDERR + 232 <= fst iv) W -> stderr_wfile m'.
Proof.
  intros m m' W (flags & mode & e & wend & tail & FC & H) MU WM FW.
  exists flags, mode, e, wend, tail. split; [| exact H].
  eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn; intros lo hi HH; lia.
Qed.

Lemma stderr_file_munch : forall m m' W,
  stderr_file m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => snd iv <= ASTDERR \/ ASTDERR + 232 <= fst iv) W -> stderr_file m'.
Proof.
  intros m m' W (flags & mode & e & wend & tail & FC) MU WM FW.
  exists flags, mode, e, wend, tail.
  eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn; intros lo hi HH; lia.
Qed.

Lemma stdin_file_munch : forall m m' W,
  stdin_file m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => snd iv <= ASTDIN \/ ASTDIN + 232 <= fst iv) W -> stdin_file m'.
Proof.
  intros m m' W (tail & FC) MU WM FW. exists tail.
  eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. eapply disjoint_from_Forall; [exact FW|]. cbn; intros lo hi HH; lia.
Qed.

(* [comment removed for export] *)
Definition afile_addr (a : Z) : Prop :=
  (ASTDOUT <= a < ASTDOUT + 232) \/ (ASTDOUT_BUF <= a < ASTDOUT_BUF + 1024) \/ (ASTDERR <= a < ASTDERR + 232) \/ (ASTDIN <= a < ASTDIN + 232).

Lemma stdout_file_magree : forall m m' so (P : Z -> Prop),
  stdout_file m so -> magree P m m' -> (forall a, (ASTDOUT <= a < ASTDOUT + 232) \/ (ASTDOUT_BUF <= a < ASTDOUT_BUF + 1024) -> P a) -> stdout_file m' so.
Proof.
  intros m m' so P (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) AG HP.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_magree; [exact AG| exact FC| cbn; intros; apply HP; cbn; lia].
  - eapply rw_cells_magree; [exact AG| exact BUF| cbn; intros; apply HP; cbn; lia].
Qed.

Lemma stderr_wfile_magree : forall m m' (P : Z -> Prop),
  stderr_wfile m -> magree P m m' -> (forall a, ASTDERR <= a < ASTDERR + 232 -> P a) -> stderr_wfile m'.
Proof.
  intros m m' P (flags & mode & e & wend & tail & FC & H) AG HP.
  exists flags, mode, e, wend, tail. split; [| exact H].
  eapply rw_cells_magree; [exact AG| exact FC| cbn; intros; apply HP; cbn; lia].
Qed.

Lemma stdin_file_magree : forall m m' (P : Z -> Prop),
  stdin_file m -> magree P m m' -> (forall a, ASTDIN <= a < ASTDIN + 232 -> P a) -> stdin_file m'.
Proof.
  intros m m' P (tail & FC) AG HP. exists tail.
  eapply rw_cells_magree; [exact AG| exact FC| cbn; intros; apply HP; cbn; lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma aclient_image_of : forall a,
  ADATA_LO <= a < AIMG_HI -> (a < 0xa6300 \/ 0xa6308 <= a < 0xa6358 \/ 0x5cc010 <= a) ->
  (a < 0x5dc8cc \/ 0x5dc8d0 <= a) -> aclient_image a.
Proof.
  intros a Ha Hc He. unfold aclient_image. right; right. split; [exact Ha|]. split.
  - intros (lo & hi & Hin & R). unfold ART_WSTATIC in Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  - unfold AERRNO, ATP. lia.
Qed.

Lemma adstat_client : forall sp0 LB LF SP a, adstat_addr a -> cj_client_addr sp0 LB LF SP a.
Proof.
  intros sp0 LB LF SP a Hd. right; left. apply aclient_image_of;
    unfold adstat_addr, atex_addr, A_ATEXIT, A_AEF_INIT, AINCB, ADATA_LO, AIMG_HI, ATIDCELL, AOFL_HEAD, ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED, AGOT_STDERR, ASTDERR_VAR,
      AGOT_GUARD, AGUARD, ATP in *; lia.
Qed.

Lemma ADSTAT_cj_pres : forall tid sp0 LB LF SP m m', ADSTAT tid m -> cj_pres sp0 LB LF SP m m' -> ADSTAT tid m'.
Proof.
  intros tid sp0 LB LF SP m m' D PR. eapply ADSTAT_magree; [exact D|].
  eapply magree_of_cj_pres; [exact PR|]. intros a _ Hd. apply adstat_client. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma ADSTAT_phase1 : forall tid m, ADSTAT tid m -> rw_cells bsegs m AINITFLAG [C1 (Z_to_bv 8 0)] ->
  ATEX1 m /\ exists (cdt thr sec : bv 8) (tm1 : word), rw_cells bsegs m A_LIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros tid m D IFL. unfold ADSTAT in D.
  destruct D as (_ & _ & (cdt & thr & sec & tm1 & D3) & AT & _).
  split; [| exists cdt, thr, sec, tm1; exact D3].
  destruct AT as [AT1|(_ & _ & I1 & _)]; [exact AT1| exfalso].
  change A_AEF_INIT with AINITFLAG in I1.
  pose proof (proj2 (proj1 IFL)) as (_ & _ & B0). pose proof (proj2 (proj1 I1)) as (_ & _ & B1).
  pose proof (B0 0%nat ltac:(cbn; lia)) as E0. pose proof (B1 0%nat ltac:(cbn; lia)) as E1. cbn [Z.of_nat Z.add nth_error cells_bytes] in E0, E1.
  rewrite Z.add_0_r in E0, E1. rewrite E0 in E1.
  cbn [cbytes app] in E1. injection E1 as E1'. vm_compute in E1'. lia.
Qed.

Lemma ADSTAT_phase2 : forall tid m m', ADSTAT tid m -> magree (fun a => adstat_addr a /\ ~ atex_addr a) m m' -> ATEX2 m' -> ADSTAT tid m'.
Proof.
  intros tid m m' D AG AT2. unfold ADSTAT in *.
  destruct D as (D1 & D2 & (cdt & thr & sec & tm1 & D3) & D4 & D6 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & (canary & D21)).
  Ltac tr2 AG := eapply rw_cells_magree; [exact AG| eassumption| unfold adstat_addr, atex_addr; adstat_lits; cbn; intros; lia].
  split; [tr2 AG|]. split; [tr2 AG|]. split; [exists cdt, thr, sec, tm1; tr2 AG|]. split; [right; exact AT2|].
  repeat match goal with |- _ /\ _ => split end; try (exists canary); tr2 AG.
Qed.

Lemma ADSTAT_incb : forall tid m m', ADSTAT tid m -> magree (fun a => adstat_addr a /\ ~ (AINCB <= a < AINCB + 1)) m m' ->
  rw_cells bsegs m' AINCB [C1 (Z_to_bv 8 0)] -> ADSTAT tid m'.
Proof.
  intros tid m m' D AG CB. unfold ADSTAT in *.
  destruct D as (D1 & D2 & (cdt & thr & sec & tm1 & D3) & D4 & D6 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & (canary & D21)).
  Ltac tr3 AG := eapply rw_cells_magree; [exact AG| eassumption| unfold adstat_addr, atex_addr; adstat_lits; cbn; intros; lia].
  split; [tr3 AG|]. split; [tr3 AG|]. split; [exists cdt, thr, sec, tm1; tr3 AG|]. split.
  { unfold ATEX, ATEX1, ATEX2, atex_cells in *. cbn [app] in *.
    destruct D4 as [((f1 & f2 & f3 & pad & j1 & H) & (j2 & G) & C)|((f1 & f2 & f3 & pad & H) & G & I & C)].
    - left. split; [exists f1, f2, f3, pad, j1; tr3 AG| split; [exists j2; tr3 AG| exact CB]].
    - right. split; [exists f1, f2, f3, pad; tr3 AG| split; [tr3 AG| split; [tr3 AG| exact CB]]]. }
  repeat match goal with |- _ /\ _ => split end; try (exists canary); tr3 AG.
Qed.

Lemma afile_client : forall sp0 LB LF SP a, afile_addr a -> cj_client_addr sp0 LB LF SP a.
Proof.
  intros sp0 LB LF SP a Hd. right; left. apply aclient_image_of;
    unfold afile_addr, ADATA_LO, AIMG_HI, ASTDOUT, ASTDOUT_BUF, ASTDERR, ASTDIN in *; lia.
Qed.

Lemma stdout_file_cj_pres : forall sp0 LB LF SP m m' so, stdout_file m so -> cj_pres sp0 LB LF SP m m' -> stdout_file m' so.
Proof.
  intros sp0 LB LF SP m m' so H PR. eapply stdout_file_magree; [exact H| eapply magree_of_cj_pres; [exact PR| intros a _ Ha; exact Ha]|].
  intros a Ha. apply afile_client. unfold afile_addr. lia.
Qed.

Lemma stderr_wfile_cj_pres : forall sp0 LB LF SP m m', stderr_wfile m -> cj_pres sp0 LB LF SP m m' -> stderr_wfile m'.
Proof.
  intros sp0 LB LF SP m m' H PR. eapply stderr_wfile_magree; [exact H| eapply magree_of_cj_pres; [exact PR| intros a _ Ha; exact Ha]|].
  intros a Ha. apply afile_client. unfold afile_addr. lia.
Qed.

Lemma stdin_file_cj_pres : forall sp0 LB LF SP m m', stdin_file m -> cj_pres sp0 LB LF SP m m' -> stdin_file m'.
Proof.
  intros sp0 LB LF SP m m' H PR. eapply stdin_file_magree; [exact H| eapply magree_of_cj_pres; [exact PR| intros a _ Ha; exact Ha]|].
  intros a Ha. apply afile_client. unfold afile_addr. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stack_part_cj_pres : forall sp0 LB LF SP m m',
  stack_shadow_zero m -> cj_pres sp0 LB LF SP m m' -> sh_zero m' alloc_ceiling (2^47).
Proof.
  (* [comment removed for export] *)
  intros sp0 LB LF SP m m' [H _] PR. intros a Ha. pose proof (H a Ha) as S. unfold shb in *.
  pose proof (SH_mono alloc_ceiling a (proj1 Ha)) as M1.
  pose proof (SH_lt_of a (2^47) ltac:(Z.div_mod_to_equations; lia)) as M2.
  pose proof SSZ_LO_le as LE. unfold SSZ_LO in LE.
  rewrite SSZ_HI_eq in M2. unfold SSZ_HI in M2.
  destruct (PR (SH a) ltac:(lia) ltac:(do 4 right; unfold astack_shadow; rewrite SSZ_HI_eq; unfold SSZ_HI; lia)) as [E _].
  rewrite E. exact S.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_at_app : forall m A cs1 cs2,
  cells_at bsegs m A (cs1 ++ cs2) <-> cells_at bsegs m A cs1 /\ cells_at bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app. split.
  - intros [[W1 W2] [B1 B2]]. rewrite cells_bytes_length in B2 by exact W1. tauto.
  - intros [[W1 B1] [W2 B2]]. rewrite cells_bytes_length by exact W1. tauto.
Qed.

Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at bsegs m A (n1 + n2) <-> wr_at bsegs m A n1 /\ wr_at bsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). repeat split; try lia; intros i Hi; [apply H; lia|].
    replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hl & HA) & (Hb & Hl2 & HB)). split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i n1); [apply HA; lia|]. replace (A + i) with (A + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells bsegs m A (cs1 ++ cs2) <-> rw_cells bsegs m A cs1 /\ rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells. rewrite cells_at_app, cells_size_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.

Lemma rw_cells_take : forall m A cs1 cs2, rw_cells bsegs m A (cs1 ++ cs2) -> rw_cells bsegs m A cs1.
Proof. intros m A cs1 cs2 H. apply rw_cells_app in H. tauto. Qed.
Lemma rw_cells_drop : forall m A cs1 cs2, rw_cells bsegs m A (cs1 ++ cs2) -> rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. intros m A cs1 cs2 H. apply rw_cells_app in H. tauto. Qed.
(* [comment removed for export] *)
Lemma rw_cells_uncons : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c] /\ rw_cells bsegs m (A + Z.of_nat (Cells.csize c)) cs.
Proof. intros m A c cs H. apply (rw_cells_app m A [c] cs) in H. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.
Lemma rw_cells_glue : forall m A cs1 cs2 B, rw_cells bsegs m A cs1 -> rw_cells bsegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells bsegs m A (cs1 ++ cs2).
Proof. intros m A cs1 cs2 B H1 H2 ->. apply rw_cells_app. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_eq_emit : forall o K K', t_eq K K' -> t_eq (t_emit o K) (t_emit o K').
Proof.
  intros o K K' H tr. unfold t_emit. split; intros [Hp | (tr' & -> & HK)]; try (left; exact Hp); right; exists tr'; split; auto; apply H; exact HK.
Qed.

Lemma t_exit_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit, t_emit. left. apply is_prefix_nil. Qed.

Lemma t_emit_has_nil' : forall o K, t_emit o K [].
Proof. intros. unfold t_emit. left. apply is_prefix_nil. Qed.

(* [comment removed for export] *)
Lemma lrz_drop_nil : forall ms mo g K, K [] -> LRZ bsegs ms mo g (t_emit (W 1 []) K) -> LRZ bsegs ms mo g K.
Proof. intros ms mo g K HK H. eapply lrz_conseq; [exact H|]. cbn [W map]. apply t_emit_nil_eq. exact HK. Qed.

Lemma lrz_die : forall ms mo g msg fs,
  LRZ bsegs ms mo g (t_emit (W 2 msg) (t_emit (W 1 []) (t_exit (wz 2) fs))) -> LRZ bsegs ms mo g (t_die msg fs).
Proof.
  intros ms mo g msg fs H. unfold t_die. eapply lrz_conseq; [exact H|]. apply t_eq_emit. cbn [W map]. apply t_emit_nil_eq. apply t_exit_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition spec_path (path : list byte) (fs0 : Fs) : TSet :=
  if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
  else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
  else if list_byte_eqb path dot_path then t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
  else match fs_lookup fs0 path with
       | None => t_die (msg_cannot_open path) fs0
       | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)
       end.

Lemma spec_two : forall a0 path fs0, spec [a0; path] fs0 = spec_path path fs0.
Proof. reflexivity. Qed.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

Lemma list_byte_eqb_neq : forall p q, list_byte_eqb p q = false <-> p <> q.
Proof.
  intros p q. destruct (list_byte_eqb p q) eqn:E.
  - apply list_byte_eqb_eq in E. split; [discriminate| intros H; exfalso; exact (H E)].
  - split; [| reflexivity]. intros _ H. apply (proj2 (list_byte_eqb_eq p q)) in H. congruence.
Qed.

(* [comment removed for export] *)
Lemma alloc_ceiling_lit : alloc_ceiling = alloc_ceiling.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma errno_addr_tp : forall tp, tp = wz ATP -> bv_unsigned tp + -164 = AERRNO.
Proof. intros tp ->. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_alt2_idem_l : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. split; intros H; [destruct H as [H|[H|H]]| destruct H as [H|H]]; auto. Qed.

Lemma t_body_nil : forall data fs, t_body data fs [].
Proof.
  intros data fs. unfold t_body, t_die. cbv zeta.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply t_emit_has_nil'|].
  destruct (length data <? 6)%nat; [apply t_emit_has_nil'|].
  destruct (length data <? 6 + Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat; [apply t_emit_has_nil'|].
  apply t_emit_has_nil'.   (* [comment removed for export] *)
Qed.

Lemma rw_cells_bytes_at : forall m A cs, rw_cells bsegs m A cs -> bytes_at bsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ HB] _]. exact HB. Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells bsegs m A [CB n bs] -> bytes_at bsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[WF HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. cbn in WF. destruct WF as [WF _]. split; [exact HB| exact WF].
Qed.


End CeilWrap.
