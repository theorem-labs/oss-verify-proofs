(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segD.v, with its module paths and module names changed; 1714 of its 1814 lines of code are new or changed and 1932 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): segment S13 of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): the statement
   lt_seg_S13_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, from the cut K85994 (0x85994, after the two callocs) to
   the cuts K85b0c (turn 0 of the m_declared loop) and K85e50 (past the loop). The code it walks:
   0x85994 .. 0x859c0: the UBSan trap on `&tab[cap]` (refuted: tab is a heap block below 2^47, 18 * cap < 720) and
   memset(&tab[cap], 0x5a, 18) through the checked memset entry; 0x859c4 .. 0x859ec: n comes into scope (its shadow
   byte := 4) and n := 0; the seed of the VLAN tables when flags & 1 and cap > 0 (0x859f0 .. 0x85a80: two UBSan
   alignment traps refuted by the blocks' 16-byte alignment, two checked memcpy of the literal "enp1s0" (0x21060,
   the listing's object 9) into tab and mt, the two instrumented checks of tab + 16 and mt + 16 discharged by the
   blocks' addressable range, the stores of the VLAN 33 and n := 1), else (0x85a84) none; 0x85a98 .. 0x85ab8: the
   instrumented check of m->n and the branch on m->n <= 0. The pure lemmas this segment uses are in
   LLVMFuzzerTestOneInput_s21k.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase SegAddr SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s21k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws: image B's kit proves them (lib/B/YG0q.v AR_laws_ok) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the listing's object values (lib/B/Prog/SegObj.v), as the S01 / S02 and S11 / S12 walks take it *)
Hypothesis VOBJS : seg_val_objs.
(* the checked memset and memcpy entries (YG0d.aintrin_realizes OSet / OCpy) *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Definition s21_E (regs : bvmap 5 word) (fr sh m cap fl mn : Z) : env :=
  Eimg (PI := PI) (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 fr; Z_to_bv 64 sh; Z_to_bv 64 m; Z_to_bv 64 cap;
                              Z_to_bv 64 fl; Z_to_bv 64 mn]).
Definition s21_G (ta ma : nat) : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, PaLibF.HPTR 5); (35%nat, PaLibF.HPTR 4); (36%nat, mkAF 0 39 0);
           (ta, PaLibF.HPTR 4); (ma, PaLibF.HPTR 4)] [] [].
Lemma s21_E_reg : forall regs fr sh m cap fl mn n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (s21_E regs fr sh m cap fl mn) n = getr regs r.
Proof.
intros regs fr sh m cap fl mn n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s21_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
Lemma s21_E_x : forall regs fr sh m cap fl mn (j : nat) v, (j < 7)%nat ->
  nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 fr; Z_to_bv 64 sh; Z_to_bv 64 m; Z_to_bv 64 cap; Z_to_bv 64 fl; Z_to_bv 64 mn] (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew (s21_E regs fr sh m cap fl mn) (32 + j) = Z_to_bv 64 v.
Proof.
intros regs fr sh m cap fl mn j v Hj Hn. unfold s21_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. exact Hn.
Qed.
Lemma s21_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv. cbn [sv_denot]. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma s21_chunk8 : forall E mem base o e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS mem (base + o) 8 v -> YP09.chunk_ok SEGS E mem base {| c_off := o; YP09.c_val := CVal 8 e |}.
Proof. intros E mem base o e v H Hv Hm. apply (chunk_ok_val SEGS E mem base o 8 e v H); [cbn; lia | cbn; lia | exact Hm]. Qed.


Lemma s21_U_mul : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= v * k < 2 ^ 64 ->
  U E (SMd M_MUL (SOff n 0) (SLit k)) = v * k.
Proof.
intros E n v k H Hv Hk Hvk. unfold U. cbn [sv_denot mul_div]. rewrite bv_mul_unsigned.
rewrite H, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small v (2 ^ 64) Hv), Z.add_0_r, (Z.mod_small v (2 ^ 64) Hv), (Z.mod_small k (2 ^ 64) Hk). apply Z.mod_small. exact Hvk.
Qed.
Lemma s21_rdword_rng : forall segs H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v Hr. unfold rdword in Hr.
repeat match type of Hr with context [aview segs H mem ?x] =>
  let b := fresh "b" in let Eb := fresh "Eb" in
  destruct (aview segs H mem x) as [b|] eqn:Eb; [pose proof (sa_aview_rng segs H mem x b Eb) | discriminate Hr] end.
injection Hr as <-. lia.
Qed.

Definition Bsp : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).


Ltac s21_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.


Lemma s21_pw_nodup : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) ->
  pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos H; [constructor|]. cbn [map pairwise] in H. destruct H as (H1 & H2).
constructor; [|exact (IH (fun b Hb => Hpos b (or_intror Hb)) H2)]. intros Hin.
pose proof (Hpos x (or_introl eq_refl)) as Hx.
apply (in_map (fun b : Z * Z => (fst b, req_size (snd b)))) in Hin.
rewrite Forall_forall in H1. specialize (H1 _ Hin). unfold zdisjoint in H1. cbn [fst snd] in H1.
destruct x as [p n]. cbn [fst snd] in H1, Hx. unfold req_size in H1. destruct (n =? 0) eqn:En.
- lia.
- apply Z.eqb_neq in En. lia.
Qed.
Lemma s21_blocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (ablocks B ly S) as [|[p n] l] eqn:El; [constructor|].
assert (Hin : In (p, n) (ablocks B ly S)) by (rewrite El; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite El in Hpw. apply (s21_pw_nodup _); [|exact Hpw].
intros [b q] Hb. rewrite <- El in Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & _ & _ & _ & _ & _ & Hq).
cbn [snd]. lia.
Qed.
Lemma s21_notin_bl0 : forall cx ly S (W : world SEGS) mem md O x, AR SEGS B ly S W mem md -> lt_blocks B cx ly S O ->
  In x O -> ~ In x (x_bl0 B cx).
Proof.
intros cx ly S W mem md O x HAR Hbl Hx Hx0.
pose proof (Permutation_NoDup Hbl (s21_blocks_nodup ly S W mem md HAR)) as Hnd. clear Hbl.
revert Hx Hx0 Hnd. generalize (x_bl0 B cx) as l0. intros l0.
induction O as [|y O IH]; intros Hx Hx0 Hnd; [destruct Hx|]. cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as (Hn & Hnd).
destruct Hx as [<- | Hx]; [apply Hn, in_or_app; right; exact Hx0 | exact (IH Hx Hx0 Hnd)].
Qed.
Lemma s21_blk_off_fp : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ inFP (ltoi_PG longlA) a.
Proof.
intros ly S W mem md p n a HAR Hin Ha (r & Hr & Hlo & Hhi).
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
cbn [ltoi_PG In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi.
unfold longlA, A_LONGL, LONGL_N in *. lia.
Qed.


Definition s21_sl1 (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 128 wlo whi
    [YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 256));
     YP09.mkChunk 56 (CVal 8 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 32))].
Definition s21_sl2 (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 128 224 wlo whi
    [YP09.mkChunk 176 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 35 0x2000) (SLit 3)) (SOff 32 0)));
     YP09.mkChunk 184 (CVal 8 (SOff 34 0)); YP09.mkChunk 192 (CVal 8 (SOff 35 0));
     YP09.mkChunk 200 (CVal 8 (SOff 32 0)); YP09.mkChunk 216 (CVal 8 (SOff 35 0x2000))].
Lemma s21_seed2 : forall pc (ta ma : nat) (rt rm : bv 5) w1 h1 w2 h2 (W : world SEGS) regs mem s1 fr m cap fl mn tv mv,
  Z.of_nat ta = bv_unsigned rt -> Z.of_nat ma = bv_unsigned rm ->
  regions_wf [s21_sl1 w1 h1; s21_sl2 w2 h2] = true -> 16 <= w1 -> h1 <= 128 -> 128 <= w2 -> h2 <= 224 ->
  getr regs 9 = w64 s1 -> getr regs 2 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  (forall o, 16 <= o < 224 -> apresent (w_H W) mem (s1 + o)) ->
  4096 <= fr <= 140737479966720 -> fr mod 32 = 0 ->
  4096 <= m <= 140737479966720 -> m mod 16 = 0 -> 0 <= cap < 40 -> 0 <= fl < 2 ^ 64 -> 0 <= mn < 2 ^ 64 ->
  getr regs rt = w64 tv -> 4096 <= tv <= 140737479966720 -> tv mod 16 = 0 ->
  getr regs rm = w64 mv -> 4096 <= mv <= 140737479966720 -> mv mod 16 = 0 ->
  rdword (rdW W mem) (s1 + 32) = Some fl -> rdword (rdW W mem) (s1 + 48) = Some (fr + 256) ->
  rdword (rdW W mem) (s1 + 56) = Some cap -> rdword (rdW W mem) (s1 + 64) = Some (fr + 32) ->
  rdword (rdW W mem) (s1 + 176) = Some (shadow_addr (m + 0x2000)) ->
  rdword (rdW W mem) (s1 + 184) = Some (shadow_addr fr) -> rdword (rdW W mem) (s1 + 192) = Some m ->
  rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF -> rdword (rdW W mem) (s1 + 216) = Some (m + 0x2000) ->
  st_ok_pi SEGS VAL (s21_E regs fr (shadow_addr fr) m cap fl mn)
    (mkSS pc sr_atoms [s21_sl1 w1 h1; s21_sl2 w2 h2] None (s21_G ta ma))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc ta ma rt rm w1 h1 w2 h2 W regs mem s1 fr m cap fl mn tv mv Hta Hma HWF Hw1 Hh1 Hw2 Hh2 R9 R2 Hs1 Hs1a Hpr
  Hfr Hfra Hm Hma16 Hcap Hfl Hmn Rt Htv Htva Rm Hmv Hmva S32 S48 S56 S64 S176 S184 S192 S200 S216.
set (E := s21_E regs fr (shadow_addr fr) m cap fl mn).
assert (EV : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n r v Hn Hr Hv. unfold E. rewrite (s21_E_reg _ _ _ _ _ _ _ n r Hn), Hr. unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (s21_E_x _ _ _ _ _ _ _ 0 _ ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 fr) by exact (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr fr)) by exact (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 m) by exact (s21_E_x _ _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 cap) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 fl) by exact (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl).
assert (U9 : bv_unsigned (ew E 9) = s1) by (apply (EV 9%nat 9%bv); [reflexivity | exact R9 | lia]).
assert (U2 : bv_unsigned (ew E 2) = s1) by (apply (EV 2%nat 2%bv); [reflexivity | exact R2 | lia]).
assert (Ut : bv_unsigned (ew E ta) = tv) by (apply (EV ta rt); [exact Hta | exact Rt | lia]).
assert (Um : bv_unsigned (ew E ma) = mv) by (apply (EV ma rm); [exact Hma | exact Rm | lia]).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr fr < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound fr 8 (2 ^ 61)); pose proof (Z.div_pos fr 8); lia).
assert (Hsm : 0 <= shadow_addr (m + 0x2000) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (m + 0x2000) 8 (2 ^ 61)); pose proof (Z.div_pos (m + 0x2000) 8); lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, s21_E. apply regs_ok_Eimg_Ereg.
- exact HWF.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold s21_sl1, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpr; lia|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 32 _ fl); [rewrite (s21_den_off E 37 fl 0 E37), Z.add_0_r by lia; reflexivity | lia | exact (val_mem_of_rdword SEGS _ _ _ _ S32)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 48 _ (fr + 256)); [rewrite (s21_den_off E 33 fr 256 E33) by lia; reflexivity | lia | exact (val_mem_of_rdword SEGS _ _ _ _ S48)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 56 _ cap); [rewrite (s21_den_off E 36 cap 0 E36), Z.add_0_r by lia; reflexivity | lia | exact (val_mem_of_rdword SEGS _ _ _ _ S56)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 64 _ (fr + 32)); [rewrite (s21_den_off E 33 fr 32 E33) by lia; reflexivity | lia | exact (val_mem_of_rdword SEGS _ _ _ _ S64)]|].
    apply Forall_nil.
  + unfold s21_sl2, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpr; lia|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 176 _ (shadow_addr (m + 0x2000))); [rewrite (denot_shx E 35 32 0x2000 m SHADOW_OFF E35 E32) by (unfold SHADOW_OFF; lia); unfold shadow_addr; f_equal; lia | exact Hsm | exact (val_mem_of_rdword SEGS _ _ _ _ S176)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 184 _ (shadow_addr fr)); [rewrite (s21_den_off E 34 _ 0 E34), Z.add_0_r by exact Hsf; reflexivity | exact Hsf | exact (val_mem_of_rdword SEGS _ _ _ _ S184)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 192 _ m); [rewrite (s21_den_off E 35 m 0 E35), Z.add_0_r by lia; reflexivity | lia | exact (val_mem_of_rdword SEGS _ _ _ _ S192)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 200 _ SHADOW_OFF); [rewrite (s21_den_off E 32 _ 0 E32), Z.add_0_r by (unfold SHADOW_OFF; lia); reflexivity | unfold SHADOW_OFF; lia | exact (val_mem_of_rdword SEGS _ _ _ _ S200)]|].
    apply Forall_cons; [apply (s21_chunk8 E _ s1 216 _ (m + 0x2000)); [rewrite (s21_den_off E 35 m 0x2000 E35) by lia; reflexivity | lia | exact (val_mem_of_rdword SEGS _ _ _ _ S216)]|].
    apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. split; [|split; exact I].
  split; [|exact I]. unfold extent_disjoint, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val s21_sl1 s21_sl2]. rewrite U9. lia.
- split; [|split; [exact I | exact I]].
  cbn [s21_G f_atoms atoms_ok]. unfold afact_ok, PaLibF.HPTR. cbn [af_lo af_hi af_al2].
  rewrite U9, U2, Ut, Um, (BU 32%nat SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)), (BU 33%nat fr E33 ltac:(lia)),
    (BU 35%nat m E35 ltac:(lia)), (BU 36%nat cap E36 ltac:(lia)).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.


Definition s21_cut cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt : Prop :=
  lt_base B MT cx /\ sa_frm0 /\
  lt_core B MT cx ly S W regs0 mem0 md0 k acc 4 LFO0
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem0) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem0) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem0) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem0) mt (x_mtn cx) /\
  zero_atA (rdW W mem0) tab (x_tabn cx) /\ zero_atA (rdW W mem0) mt (x_mtn cx) /\
  lt_slots cx (rdW W mem0) (LT_LC cx c m ++ [(176, shadow_addr (m + seg_spec.MC_N))]) /\
  lt_cm (rdW W mem0) c m (x_run cx).
Definition s21_jr cx ly S (W : world SEGS) memX mdX k : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memX mdX k.
Definition s21_rg cx (regsX : bvmap 5 word) : Prop :=
  getr regsX 2 = w64 (x_s1 cx) /\ getr regsX 3 = getr (x_regs cx) 3 /\ getr regsX 4 = getr (x_regs cx) 4 /\
  getr regsX 8 = w64 (x_sp0 cx) /\ getr regsX 9 = w64 (x_s1 cx).
Definition s21_ptB cx ly S (W : world SEGS) mem0 k tab mt regsB memB mdB : Prop :=
  s21_jr cx ly S W memB mdB k /\ s21_rg cx regsB /\ getr regsB 18 = w64 tab /\ getr regsB 19 = w64 mt /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
     ~ (tab + 18 * x_cap cx <= a < tab + 18 * x_cap cx + 18) -> rdW W memB a = rdW W mem0 a) /\
  (forall i, 0 <= i < 18 -> rdW W memB (tab + 18 * x_cap cx + i) = Some 0x5a).
Definition s21_ws cx tab mt a : Prop :=
  (x_s1 cx - 4096 <= a < x_s1 cx) \/ (x_s1 cx + 88 <= a < x_s1 cx + 168) \/ (tab <= a < tab + x_tabn cx) \/
  (mt <= a < mt + x_mtn cx) \/ (x_fr cx + 256 <= a < x_fr cx + 260) \/ a = x_sh cx + 32.
Definition s21_ptJ cx ly S (W : world SEGS) mem0 k tab mt regsJ memJ mdJ : Prop :=
  s21_jr cx ly S W memJ mdJ k /\ s21_rg cx regsJ /\ getr regsJ 16 = w64 SHADOW_OFF /\
  getr regsJ 18 = w64 tab /\ getr regsJ 19 = w64 mt /\ getr regsJ 20 = w64 (mt + 16) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rdW W memJ a = rdW W mem0 a) /\
  rdword (rdW W memJ) (x_s1 cx + 128) = Some (Z.of_nat (length (x_tab0 cx))) /\
  rdword (rdW W memJ) (x_s1 cx + 160) = Some 1 /\
  rdW W memJ (x_sh cx + 32) = Some 4 /\
  sa_val (rdW W memJ) (x_fr cx + FO_N) 4 (Z.of_nat (length (x_tab0 cx))) /\
  sa_rtab (rdW W memJ) tab (x_tab0 cx) /\ sa_guardtab (rdW W memJ) tab (x_cap cx) /\
  sa_mtab (rdW W memJ) mt (x_tab0 cx).


Lemma s21_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.


Ltac s21_kept HFr Zs fin :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn;
  lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
  refine (kept_of_frame Ex rsx H m0 m1 Zs HFr _ a Ha Hn);
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros bb wlo whi x Hin Hr;
  let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
  fin Hr
  end.


Definition s21_ptA cx ly S (W : world SEGS) mem0 k tab mt regsA memA mdA : Prop :=
  s21_jr cx ly S W memA mdA k /\ s21_rg cx regsA /\ getr regsA 18 = w64 tab /\ getr regsA 19 = w64 mt /\
  getr regsA 20 = w64 (mt + 16) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
     ~ (tab + 18 * x_cap cx <= a < tab + 18 * x_cap cx + 18) -> ~ (x_fr cx + 256 <= a < x_fr cx + 260) ->
     a <> x_sh cx + 32 -> rdW W memA a = rdW W mem0 a) /\
  (forall i, 0 <= i < 18 -> rdW W memA (tab + 18 * x_cap cx + i) = Some 0x5a) /\
  rdW W memA (x_sh cx + 32) = Some 4 /\ sa_val (rdW W memA) (x_fr cx + FO_N) 4 0.
Definition s21_fsh : YP09.region := YP09.mkRegion (Some 34%nat) 32 33 32 33 [].
Definition s21_frn : YP09.region := YP09.mkRegion (Some 33%nat) 256 260 256 260 [].


Lemma s21_rdword_keep : forall (rd rd' : reader) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v HK HR. unfold rdword in *.
pose proof (HK 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
rewrite K0, (HK 1 ltac:(lia)), (HK 2 ltac:(lia)), (HK 3 ltac:(lia)),
  (HK 4 ltac:(lia)), (HK 5 ltac:(lia)), (HK 6 ltac:(lia)), (HK 7 ltac:(lia)).
exact HR.
Qed.


Ltac s21_fold KR Zs fin :=
  lazymatch type of KR with forall a, _ -> _ -> aview _ (w_H ?W) ?mc a = aview _ _ ?mb a =>
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict _ mc) (mrestrict _ ?m1) |- _ =>
    let K2 := fresh "KR" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mb a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn; refine (eq_trans _ (KR a Ha Hn)); revert a Ha Hn; s21_kept HFr Zs fin
    | clear KR HFr; rename K2 into KR ] end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end.


Lemma s21_den0 : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma s21_denc : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv. exact (s21_den_off E n v c H Hv). Qed.
Lemma s21_val1 : forall (W : world SEGS) mem a v, val_mem SEGS (mrestrict (w_H W) mem) a 1 v -> 0 <= v < 256 ->
  rdW W mem a = Some v.
Proof. intros W mem a v H Hv. exact (PaLibF.aview_of_val_mem1 SEGS (w_H W) mem a v H Hv). Qed.


Lemma s21_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.


Definition s21_mn : YP09.region := YP09.mkRegion (Some 35%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 38 0))].


Lemma s21_sep_sz : forall ly S (W : world SEGS) mem md p n q n', AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (q, n') (ablocks B ly S) -> n <> n' -> zdisjoint (p, req_size n) (q, req_size n').
Proof.
intros ly S W mem md p n q n' HAR H1 H2 Hn. apply (sep_blocks SEGS B LAWS ly S W mem md p n q n' HAR H1 H2).
intros Hq. injection Hq as _ Hq. exact (Hn Hq).
Qed.
Definition s21_lay cx (tab mt : Z) : Prop :=
  alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\ x_sp0 cx <= 2 ^ 47 /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  2147450880 <= x_sh cx /\ x_sh cx + 64 <= 17594333495296 /\
  4096 <= tab /\ tab + x_tabn cx <= alloc_ceiling /\ in_app tab (x_tabn cx) /\ 18 <= x_tabn cx /\
  4096 <= mt /\ mt + x_mtn cx <= alloc_ceiling /\ in_app mt (x_mtn cx) /\ 20 <= x_mtn cx /\
  zdisjoint (tab, x_tabn cx) (x_fr cx, 512) /\ zdisjoint (mt, x_mtn cx) (x_fr cx, 512) /\
  zdisjoint (tab, x_tabn cx) (mt, x_mtn cx) /\ off_img tab (x_tabn cx) /\ off_img mt (x_mtn cx) /\
  off_img (x_fr cx) 512 /\ 140735332483072 <= alloc_ceiling <= 140737479966720.
Lemma s21_nws_blk : forall cx tab mt p n a, s21_lay cx tab mt ->
  zdisjoint (p, n) (tab, x_tabn cx) -> zdisjoint (p, n) (mt, x_mtn cx) -> zdisjoint (p, n) (x_fr cx, 512) ->
  in_app p n -> p + n <= alloc_ceiling -> p <= a < p + n -> ~ s21_ws cx tab mt a.
Proof.
intros cx tab mt p n a HL D1 D2 D3 Hp Hc Ha.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
unfold zdisjoint, in_app, s21_ws, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. cbn [fst snd] in *. lia.
Qed.
Lemma s21_nws_fr : forall cx tab mt a, s21_lay cx tab mt ->
  x_fr cx <= a < x_fr cx + 512 -> ~ (x_fr cx + 256 <= a < x_fr cx + 260) -> ~ s21_ws cx tab mt a.
Proof.
intros cx tab mt a HL Ha Hn.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & D1 & D2 & _).
unfold zdisjoint, in_app, s21_ws, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. cbn [fst snd] in *. lia.
Qed.
Lemma s21_nws_sh : forall cx tab mt a, s21_lay cx tab mt ->
  x_sh cx <= a < x_sh cx + 64 -> a <> x_sh cx + 32 -> ~ s21_ws cx tab mt a.
Proof.
intros cx tab mt a HL Ha Hn.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & _ & _ & _ & _ & _ & _ & L17).
unfold in_app, s21_ws, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma s21_nws_stk : forall cx tab mt a, s21_lay cx tab mt ->
  (x_s1 cx <= a < x_s1 cx + 88 \/ x_s1 cx + 168 <= a < x_sp0 cx) -> ~ s21_ws cx tab mt a.
Proof.
intros cx tab mt a HL Ha.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & _ & _ & _ & _ & _ & _ & L17).
unfold s21_ws in *. lia.
Qed.
Lemma s21_nws_img : forall cx tab mt a, s21_lay cx tab mt -> 0x10000 <= a < kImgEnd -> ~ s21_ws cx tab mt a.
Proof.
intros cx tab mt a HL Ha.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & _ & _ & _ & O1 & O2 & O3 & L17).
unfold off_img, s21_ws, kImgEnd in *. lia.
Qed.


Ltac s21_unpack Hcut :=
  lazymatch type of Hcut with s21_cut ?cx ?ly ?S ?W ?regs0 ?mem0 ?md0 ?k ?acc ?c ?m ?tab ?mt =>
  destruct Hcut as (Hbase & Hfrm & Hcore & Hhc & Hhm & Hht & Hhmt & Hzt & Hzmt & Hsl & Hcm);
  pose proof Hcore as (HFR0 & Himg & Hbl & Hbud);
  destruct HFR0 as (HJ0 & R02 & R03 & R04 & R08 & R09 & Hsv & Fh0 & Fh8 & Fh16 & Ffl & S200 & Fsh & S184);
  pose proof HJ0 as (HAR0 & HLY & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _);
  pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _);
  pose proof Hbase as (Hpre & _);
  pose proof Hpre as (_ & _ & _ & Hgp & Htp & _);
  pose proof asan_consts as (C1 & _);
  pose proof alloc_ceiling_value as (C2 & _);
  assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity;
  assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity);
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hfra & Hfapp & Hfpres & Hfshp);
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hfr4 & Hfrc & _);
  assert (Efr : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by
    (destruct HLY as (_ & _ & _ & _ & _ & HF & _); unfold x_fr, frame_addr; rewrite HF; reflexivity);
  assert (HF512 : fs_frame_bytes LT_FCLS = 512) by reflexivity;
  rewrite Efr in Hfra, Hfapp, Hfpres, Hfshp, Hfr4, Hfrc; rewrite HF512 in Hfapp, Hfpres, Hfshp, Hfrc;
  assert (Hs1 : x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0) by
    (unfold x_s1, LT_FRAME; pose proof (Z.mod_pos_bound (x_sp0 cx - 352) 32 ltac:(lia)); split; [lia|];
     rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity);
  destruct Hs1 as (Hs1 & Hs1a);
  pose proof (Hsl 32 (x_flags cx) ltac:(cbn; tauto)) as S32;
  pose proof (Hsl 48 (x_fr cx + FO_N) ltac:(cbn; tauto)) as S48;
  pose proof (Hsl 56 (x_cap cx) ltac:(cbn; tauto)) as S56;
  pose proof (Hsl 64 (x_fr cx + FO_V) ltac:(cbn; tauto)) as S64;
  pose proof (Hsl 176 (shadow_addr (m + seg_spec.MC_N)) ltac:(cbn; tauto)) as S176;
  pose proof (Hsl 192 m ltac:(cbn; tauto)) as S192;
  pose proof (Hsl 216 (m + seg_spec.MC_N) ltac:(cbn; tauto)) as S216;
  pose proof Hht as (Hint & Ht4 & Hta & _); pose proof Hhmt as (Hinmt & Hmt4 & Hmta & _);
  pose proof Hhm as (Hinm & Hm4 & Hma & _); pose proof Hhc as (Hinc & Hc4 & Hca & _);
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hint) as (_ & _ & Htc & Htapp & _);
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinmt) as (_ & _ & Hmtc & Hmtapp & _);
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinm) as (_ & _ & Hmc & Hmapp & _);
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinc) as (_ & _ & Hcc & Hcapp & _);
  pose proof (s21_cap_range cx) as Hcap;
  assert (Htabn : 18 <= x_tabn cx <= 720) by (unfold x_tabn, seg_spec.RVLAN_SIZE; lia);
  assert (Hmtn : 20 <= x_mtn cx <= 800) by (unfold x_mtn, seg_spec.MVLAN_SIZE; lia);
  assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity; assert (HCS : seg_spec.SEG_C_SIZE = 16616) by reflexivity;
  rewrite (s21_req (x_tabn cx)) in Htc, Htapp by lia; rewrite (s21_req (x_mtn cx)) in Hmtc, Hmtapp by lia;
  rewrite (s21_req seg_spec.SEG_M_SIZE), HMS in Hmc, Hmapp by (rewrite HMS; lia);
  rewrite (s21_req seg_spec.SEG_C_SIZE), HCS in Hcc, Hcapp by (rewrite HCS; lia);
  pose proof (s21_rdword_rng _ _ _ _ _ S32) as Hflr;
  pose proof (s21_mconf_n _ _ _ (proj2 Hcm)) as (HMN & HMNl);
  change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in HMN, HMNl;
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hint Hfin) as Dtf;
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hinmt Hfin) as Dmtf;
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hinm Hfin) as Dmf;
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hinc Hfin) as Dcf;
  rewrite Efr, HF512 in Dtf, Dmtf, Dmf, Dcf;
  rewrite (s21_req (x_tabn cx)) in Dtf by lia; rewrite (s21_req (x_mtn cx)) in Dmtf by lia;
  rewrite (s21_req seg_spec.SEG_M_SIZE), HMS in Dmf by (rewrite HMS; lia);
  rewrite (s21_req seg_spec.SEG_C_SIZE), HCS in Dcf by (rewrite HCS; lia);
  assert (Hsfb : 2147450880 <= x_sh cx /\ x_sh cx + 64 <= 17594333495296) by
    (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 44)); pose proof (Z.div_pos (x_fr cx) 8); lia);
  assert (Dtmt : zdisjoint (tab, x_tabn cx) (mt, x_mtn cx)) by
    (pose proof (s21_sep_sz ly S W mem0 md0 tab _ mt _ HAR0 Hint Hinmt ltac:(unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE; lia)) as D;
     rewrite (s21_req (x_tabn cx)), (s21_req (x_mtn cx)) in D by lia; exact D);
  assert (Dmt : zdisjoint (m, 9236) (tab, x_tabn cx)) by
    (pose proof (s21_sep_sz ly S W mem0 md0 m _ tab _ HAR0 Hinm Hint ltac:(rewrite HMS; lia)) as D;
     rewrite (s21_req seg_spec.SEG_M_SIZE), HMS, (s21_req (x_tabn cx)) in D by (rewrite ?HMS; lia); exact D);
  assert (Dmmt : zdisjoint (m, 9236) (mt, x_mtn cx)) by
    (pose proof (s21_sep_sz ly S W mem0 md0 m _ mt _ HAR0 Hinm Hinmt ltac:(rewrite HMS; lia)) as D;
     rewrite (s21_req seg_spec.SEG_M_SIZE), HMS, (s21_req (x_mtn cx)) in D by (rewrite ?HMS; lia); exact D);
  assert (Dct : zdisjoint (c, 16616) (tab, x_tabn cx)) by
    (pose proof (s21_sep_sz ly S W mem0 md0 c _ tab _ HAR0 Hinc Hint ltac:(rewrite HCS; lia)) as D;
     rewrite (s21_req seg_spec.SEG_C_SIZE), HCS, (s21_req (x_tabn cx)) in D by (rewrite ?HCS; lia); exact D);
  assert (Dcmt : zdisjoint (c, 16616) (mt, x_mtn cx)) by
    (pose proof (s21_sep_sz ly S W mem0 md0 c _ mt _ HAR0 Hinc Hinmt ltac:(rewrite HCS; lia)) as D;
     rewrite (s21_req seg_spec.SEG_C_SIZE), HCS, (s21_req (x_mtn cx)) in D by (rewrite ?HCS; lia); exact D);
  assert (HL : s21_lay cx tab mt);
  [ unfold s21_lay;
    pose proof (blk_off_imgP B ly S W mem0 md0 tab _ HAR0 Hint) as Ot; rewrite (s21_req (x_tabn cx)) in Ot by lia;
    pose proof (blk_off_imgP B ly S W mem0 md0 mt _ HAR0 Hinmt) as Omt; rewrite (s21_req (x_mtn cx)) in Omt by lia;
    pose proof (s21_frame_off_img B ly S W mem0 md0 _ _ HAR0 Hfin) as Of; rewrite Efr, HF512 in Of;
    refine (conj _ (conj _ (conj _ (conj Hfr4 (conj Hfrc (conj Hfapp (conj (proj1 Hsfb) (conj (proj2 Hsfb)
      (conj Ht4 (conj Htc (conj Htapp (conj (proj1 Htabn) (conj Hmt4 (conj Hmtc (conj Hmtapp (conj (proj1 Hmtn)
      (conj Dtf (conj Dmtf (conj Dtmt (conj Ot (conj Omt (conj Of C1))))))))))))))))))))));
    [ lia | exact Hs1 | lia ]
  | ]
  end.


Lemma s21_bge0 : forall v, 0 <= v < 2 ^ 63 -> branch_taken BC_GE (Z_to_bv 64 0) (Z_to_bv 64 v) = (v <=? 0).
Proof.
intros v Hv. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite (bv_swrap_small 64 0), (bv_swrap_small 64 v) by (unfold bv_half_modulus, bv_modulus; cbn; lia).
destruct (Z.ltb_spec 0 v), (Z.leb_spec v 0); cbn; lia.
Qed.


Lemma s21_neg : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SUB (SLit 0) (SOff n 0)) = w64 (- v).
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SAlu, (U_atom E n v H Hv), U_lit by lia. cbn [zalu_raw].
unfold w64, zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. f_equal; lia.
Qed.
Lemma s21_not : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = Z_to_bv 64 (lt_not (v + c)).
Proof.
intros E n v c H Hv Hvc. rewrite denot_lit_U, (YI08.U_not_off E n v c H Hv Hvc). reflexivity.
Qed.


Definition s21_q1 cx ly S (W : world SEGS) k tab mt memA regsX memX mdX : Prop :=
  s21_jr cx ly S W memX mdX k /\ s21_rg cx regsX /\ getr regsX 18 = w64 tab /\ getr regsX 19 = w64 mt /\
  getr regsX 20 = w64 (mt + 16) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) -> ~ (tab <= a < tab + 7) ->
     rdW W memX a = rdW W memA a) /\
  sa_zs (rdW W memX) tab (SegModel.S_enp ++ [0]).
Definition s21_q2 cx ly S (W : world SEGS) k tab mt memA regsY memY mdY : Prop :=
  s21_jr cx ly S W memY mdY k /\ s21_rg cx regsY /\ getr regsY 18 = w64 tab /\ getr regsY 19 = w64 mt /\
  getr regsY 20 = w64 (mt + 16) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) -> ~ (tab <= a < tab + 7) ->
     ~ (tab + 16 <= a < tab + 18) -> ~ (mt <= a < mt + 7) -> rdW W memY a = rdW W memA a) /\
  sa_zs (rdW W memY) tab (SegModel.S_enp ++ [0]) /\ rdW W memY (tab + 16) = Some 33 /\ rdW W memY (tab + 17) = Some 0 /\
  sa_zs (rdW W memY) mt (SegModel.S_enp ++ [0]).


Ltac s21_rdc HR U o D H :=
  pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region _ _ _ _ _ _ _ _ _ o 8%N _ _ HR U ltac:(cbn [In]; tauto) D ltac:(cbn; unfold lt_not, LT_VIDMAX, LT_MASK, FO_V in *; lia) ltac:(cbn; lia)) ltac:(unfold lt_not, LT_VIDMAX, LT_MASK, FO_V in *; lia)) as H.


Lemma s21_zs_keep : forall (rd rd' : reader) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite (HK (Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma s21_lit_zs : forall cx rd, lt_img B cx rd -> sa_zs rd 0x21060 (SegModel.S_enp ++ [0]).
Proof.
intros cx rd HI. destruct (s21_lit_enp B cx rd HI) as (_ & ((Hz & _) & _) & _).
rewrite (proj1 s21_lit_enp_addr) in Hz. exact Hz.
Qed.
Lemma s21_lit_addr : forall cx rd ly S (W : world SEGS) mem md, lt_img B cx rd -> AR SEGS B ly S W mem md ->
  sa_addr (aview SEGS (w_H W) mem) 0x21060 7.
Proof.
intros cx rd ly S W mem md HI HAR. destruct (s21_lit_enp B cx rd HI) as (_ & _ & Hp & _).
rewrite (proj1 s21_lit_enp_addr) in Hp. exact (Hp ly S W mem md HAR).
Qed.


Definition s21_tb : YP09.region := YP09.mkRegion (Some 18%nat) 16 18 16 18 [].
Definition s21_mb : YP09.region := YP09.mkRegion (Some 19%nat) 16 20 16 20 [].


Lemma s21_sepT : forall cx tab mt a, s21_lay cx tab mt -> tab <= a < tab + x_tabn cx ->
  ~ (x_s1 cx - 4096 <= a < x_s1 cx + 168) /\ ~ (mt <= a < mt + x_mtn cx) /\ ~ (x_fr cx <= a < x_fr cx + 512) /\
  ~ (x_sh cx <= a < x_sh cx + 64).
Proof.
intros cx tab mt a HL Ha.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 & L19 & _).
unfold zdisjoint in L17, L19. cbn [fst snd] in L17, L19. unfold in_app, kLowShadowBeg, kHighMemBeg in L11.
clear L6 L15 L18. destruct L11 as [_ [L11 | [L11 L11']]]; repeat split; lia.
Qed.
Lemma s21_sepM : forall cx tab mt a, s21_lay cx tab mt -> mt <= a < mt + x_mtn cx ->
  ~ (x_s1 cx - 4096 <= a < x_s1 cx + 168) /\ ~ (tab <= a < tab + x_tabn cx) /\ ~ (x_fr cx <= a < x_fr cx + 512) /\
  ~ (x_sh cx <= a < x_sh cx + 64).
Proof.
intros cx tab mt a HL Ha.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 & L19 & _).
unfold zdisjoint in L18, L19. cbn [fst snd] in L18, L19. unfold in_app, kLowShadowBeg, kHighMemBeg in L15.
clear L6 L11 L17. destruct L15 as [_ [L15 | [L15 L15']]]; repeat split; lia.
Qed.
Lemma s21_sepF : forall cx tab mt a, s21_lay cx tab mt -> x_fr cx <= a < x_fr cx + 512 ->
  ~ (x_s1 cx - 4096 <= a < x_s1 cx + 168) /\ ~ (x_sh cx <= a < x_sh cx + 64).
Proof.
intros cx tab mt a HL Ha.
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg in L6.
destruct L6 as [_ [L6 | [L6 L6']]]; split; lia.
Qed.
Lemma s21_wsP : forall cx tab mt a, 0 <= x_cap cx -> ~ s21_ws cx tab mt a ->
  ~ (x_s1 cx + 128 <= a < x_s1 cx + 168 \/ mt + 16 <= a < mt + 20 \/ x_fr cx + 256 <= a < x_fr cx + 260) /\
  ~ (x_s1 cx - 4096 <= a < x_s1 cx) /\ ~ (tab <= a < tab + 7) /\ ~ (tab + 16 <= a < tab + 18) /\ ~ (mt <= a < mt + 7) /\
  ~ (tab + 18 * x_cap cx <= a < tab + 18 * x_cap cx + 18) /\ ~ (x_fr cx + 256 <= a < x_fr cx + 260) /\ a <> x_sh cx + 32.
Proof.
intros cx tab mt a Hc Hn. unfold s21_ws, x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in Hn.
repeat split; lia.
Qed.

(* ==================== the exit facts: the cut's facts at the exit memory ==================== *)
Lemma s21x_bytes_keep : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof.
intros rd rd' a bs HK H i Hi. rewrite (HK (Z.of_nat i)) by lia. exact (H i Hi).
Qed.
Lemma s21_tabs_keep : forall cx (rd rd' : reader) tab mt t L,
  (forall a, 0 <= a < L -> rd' a = rd a) -> 0 <= tab -> tab + x_tabn cx <= L -> 0 <= mt -> mt + x_mtn cx <= L ->
  0 <= x_fr cx -> x_fr cx + 260 <= L ->
  lt_tabs cx rd tab mt t -> lt_tabs cx rd' tab mt t.
Proof.
intros cx rd rd' tab mt t L HK Ht0 HtL Hm0 HmL Hf0 HfL (H1 & (bs & Hbs & Lbs & Ebs) & Hg & Hv & (bm & Hbm & Lbm & Ebm) & H6).
pose proof (s21_cap_range cx) as Hc.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by (unfold x_tabn, seg_spec.RVLAN_SIZE; reflexivity).
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by (unfold x_mtn, seg_spec.MVLAN_SIZE; reflexivity).
split; [exact H1|]. split; [|split; [|split; [|split; [|exact H6]]]].
- exists bs. split; [|exact (conj Lbs Ebs)]. apply (s21x_bytes_keep rd rd' tab bs); [|exact Hbs].
  intros i Hi. apply HK. lia.
- unfold sa_guardtab in *. apply (s21x_bytes_keep rd rd' _ _); [|exact Hg].
  intros i Hi. unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi.
  apply HK. unfold seg_spec.RVLAN_SIZE. lia.
- intros kk Hk. rewrite HK by (unfold FO_N; lia). exact (Hv kk Hk).
- exists bm. split; [|exact (conj Lbm Ebm)]. apply (s21x_bytes_keep rd rd' mt bm); [|exact Hbm].
  intros i Hi. apply HK. lia.
Qed.
Lemma s21x_kstk : forall cx tab mt (rd rd' : reader), s21_lay cx tab mt ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rd' a = rd a) ->
  forall a, x_s1 cx <= a < x_s1 cx + 88 \/ x_s1 cx + 168 <= a < x_sp0 cx -> rd' a = rd a.
Proof.
intros cx tab mt rd rd' HL KE a Ha. apply KE; [|exact (s21_nws_stk cx tab mt a HL Ha)].
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 &
  L19 & L20 & L21 & L22 & L23).
lia.
Qed.
Lemma s21x_kfr : forall cx tab mt (rd rd' : reader), s21_lay cx tab mt ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rd' a = rd a) ->
  forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (x_fr cx + 256 <= a < x_fr cx + 260) -> rd' a = rd a.
Proof.
intros cx tab mt rd rd' HL KE a Ha Hn. apply KE; [|exact (s21_nws_fr cx tab mt a HL Ha Hn)].
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 &
  L19 & L20 & L21 & L22 & L23).
lia.
Qed.
Lemma s21x_ksh : forall cx tab mt (rd rd' : reader), s21_lay cx tab mt ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rd' a = rd a) ->
  forall a, x_sh cx <= a < x_sh cx + 64 -> a <> x_sh cx + 32 -> rd' a = rd a.
Proof.
intros cx tab mt rd rd' HL KE a Ha Hn. apply KE; [|exact (s21_nws_sh cx tab mt a HL Ha Hn)].
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 &
  L19 & L20 & L21 & L22 & L23).
lia.
Qed.
Lemma s21x_kimg : forall cx tab mt (rd rd' : reader), s21_lay cx tab mt ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rd' a = rd a) ->
  forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a.
Proof.
intros cx tab mt rd rd' HL KE a Ha. apply KE; [|exact (s21_nws_img cx tab mt a HL Ha)].
unfold kImgEnd in Ha. lia.
Qed.
Lemma s21x_kblk : forall cx tab mt (rd rd' : reader), s21_lay cx tab mt ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rd' a = rd a) ->
  forall p n, zdisjoint (p, n) (tab, x_tabn cx) -> zdisjoint (p, n) (mt, x_mtn cx) -> zdisjoint (p, n) (x_fr cx, 512) ->
  in_app p n -> p + n <= alloc_ceiling -> forall i, 0 <= i < n -> rd' (p + i) = rd (p + i).
Proof.
intros cx tab mt rd rd' HL KE p n D1 D2 D3 Hp Hc i Hi.
apply KE; [|exact (s21_nws_blk cx tab mt p n (p + i) HL D1 D2 D3 Hp Hc ltac:(lia))].
destruct Hp as (Hp4 & _).
destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 &
  L19 & L20 & L21 & L22 & L23).
lia.
Qed.
Lemma s21x_hblk : forall ly S (W : world SEGS) mem mem' md a n, AR SEGS B ly S W mem' md -> 0 < n ->
  lt_hblk B ly S (rdW W mem) a n -> lt_hblk B ly S (rdW W mem') a n.
Proof.
intros ly S W mem mem' md a n HAR Hn (Hin & H4 & Ha & A0 & A1 & A2 & _ & _).
assert (Rq : req_size n = n) by exact (s21_req n Hn).
split; [exact Hin|]. split; [exact H4|]. split; [exact Ha|].
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- apply (range_addressable_of_block SEGS B LAWS ly S W mem' md a n a n HAR Hin); [lia | rewrite Rq; lia].
- intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem' md a n a n HAR Hin); [lia | rewrite Rq; lia | exact Hn0].
Qed.
Lemma s21x_cm_keep : forall (rd rd' : reader) c m st,
  (forall i, 0 <= i < 16616 -> rd' (c + i) = rd (c + i)) -> (forall i, 0 <= i < 9236 -> rd' (m + i) = rd (m + i)) ->
  lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st KC KM ((bc & Hbc & Ec) & (bm & Hbm & Em)). split.
- exists bc. split; [|exact Ec]. apply (s21x_bytes_keep rd rd' c bc); [|exact Hbc].
  intros i Hi. apply KC. pose proof (proj1 Ec) as Lc. unfold seg_spec.SEG_C_SIZE in Lc. lia.
- exists bm. split; [|exact Em]. apply (s21x_bytes_keep rd rd' m bm); [|exact Hbm].
  intros i Hi. apply KM. pose proof (proj1 Em) as Lm. unfold seg_spec.SEG_M_SIZE in Lm. lia.
Qed.
Lemma s21_exit_core : forall cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt regsE memE mdE,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt ->
  s21_jr cx ly S W memE mdE k -> s21_rg cx regsE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rdW W memE a = rdW W mem0 a) ->
  rdW W memE (x_sh cx + 32) = Some 4 ->
  lt_core B MT cx ly S W regsE memE mdE k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W memE) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W memE) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W memE) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W memE) mt (x_mtn cx) /\
  lt_cm (rdW W memE) c m (x_run cx) /\ lt_slots cx (rdW W memE) (LT_LV cx c m).
Proof.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt regsE memE mdE Hcut HJ HR KE SH32.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
pose proof (proj1 HJ) as HARE.
pose proof (s21x_kstk cx tab mt (rdW W mem0) (rdW W memE) HL KE) as KS.
pose proof (s21x_kfr cx tab mt (rdW W mem0) (rdW W memE) HL KE) as KF.
pose proof (s21x_ksh cx tab mt (rdW W mem0) (rdW W memE) HL KE) as KH.
pose proof (s21x_kimg cx tab mt (rdW W mem0) (rdW W memE) HL KE) as KI.
pose proof (s21x_kblk cx tab mt (rdW W mem0) (rdW W memE) HL KE c 16616 Dct Dcmt Dcf Hcapp Hcc) as KC.
pose proof (s21x_kblk cx tab mt (rdW W mem0) (rdW W memE) HL KE m 9236 Dmt Dmmt Dmf Hmapp Hmc) as KM.
assert (KO : forall o v, 16 <= o <= 80 \/ 168 <= o <= 216 ->
  rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memE) (x_s1 cx + o) = Some v).
{ intros o v Ho Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros j Hj. apply KS. lia. }
destruct HR as (E2 & E3 & E4 & E8 & E9).
split; [|split; [|split; [|split; [|split; [|split]]]]].
- split; [|split; [|split; [exact Hbl | exact Hbud]]].
  + split; [exact HJ|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E8|].
    split; [exact E9|].
    split.
    { intros i r Hi.
      assert (Hlt : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      change (length LT_SAVED) with 13%nat in Hlt.
      apply (s21_rdword_keep (rdW W mem0)); [|exact (Hsv i r Hi)].
      intros j Hj. apply KS. right. lia. }
    split. { apply (s21_rdword_keep (rdW W mem0)); [|exact Fh0]. intros j Hj. apply KF; lia. }
    split. { apply (s21_rdword_keep (rdW W mem0)); [|exact Fh8]. intros j Hj. apply KF; lia. }
    split. { apply (s21_rdword_keep (rdW W mem0)); [|exact Fh16]. intros j Hj. apply KF; lia. }
    split. { apply (s21_rdword_keep (rdW W mem0)); [|exact Ffl]. intros j Hj. apply KF; unfold LT_FLAGW; lia. }
    split. { apply KO; [lia | exact S200]. }
    split.
    { apply (LLVMFuzzerTestOneInput_s21k.s21_fsh (rdW W mem0) (rdW W memE) (x_sh cx) Fsh); [|exact SH32].
      intros i Hi Hn. apply KH; lia. }
    apply KO; [lia | exact S184].
  + exact (s21_img_keep B cx (rdW W mem0) (rdW W memE) Himg KI).
- exact (s21x_hblk ly S W mem0 memE mdE c seg_spec.SEG_C_SIZE HARE ltac:(rewrite HCS; lia) Hhc).
- exact (s21x_hblk ly S W mem0 memE mdE m seg_spec.SEG_M_SIZE HARE ltac:(rewrite HMS; lia) Hhm).
- exact (s21x_hblk ly S W mem0 memE mdE tab (x_tabn cx) HARE ltac:(lia) Hht).
- exact (s21x_hblk ly S W mem0 memE mdE mt (x_mtn cx) HARE ltac:(lia) Hhmt).
- exact (s21x_cm_keep (rdW W mem0) (rdW W memE) c m (x_run cx) KC KM Hcm).
- intros o v Hin. cbn [LT_LV In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <-;
    (apply KO; [lia | refine (Hsl _ _ _); cbn; tauto]).
Qed.

(* ==================== stage A: 0x85994 .. the checked memset (0x859c0) ==================== *)
Lemma s21_stA : (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsB memB mdB,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptB cx ly S W mem0 k tab mt regsB memB mdB ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsB (Z_to_bv 64 (BASE + 0xc04)) memB (seg_rom SEGS)) mdB) (lt_post B MT cx)) -> LTA_K85b0c B MT 0 -> LTA_K85e50 B MT -> LT_K85994_stmt B MT.
Proof.
intros HSTB HK0 HKE. unfold LT_K85994_stmt.
intros cx ly S W regs mem md k acc c m tab mt Hbase Hfrm Hcore Hhc Hhm Hht Hhmt Hzt Hzmt H10 H18 Hsl Hcm.
assert (Hcut : s21_cut cx ly S W regs mem md k acc c m tab mt) by exact (conj Hbase (conj Hfrm (conj Hcore (conj Hhc (conj Hhm (conj Hht (conj Hhmt (conj Hzt (conj Hzmt (conj Hsl Hcm)))))))))).
clear Hbase Hfrm Hcore Hhc Hhm Hht Hhmt Hzt Hzmt Hsl Hcm.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
pose proof (s21_seed2 LO_K85994 18 10 18%bv 10%bv 16 16 128 128 W regs mem (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R09 R02 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres0; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) H18 ltac:(lia) Hta H10 ltac:(lia) Hmta S32 S48 S56 S64 S176 S184 S192 S200 S216) as HS.


set (E := s21_E regs (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
assert (E18 : ew E 18 = Z_to_bv 64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl), H18; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (x_cap cx)) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl), R02; reflexivity).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R03; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R04; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl), R08; reflexivity).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl), R09; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 10 10%bv eq_refl), H10; reflexivity).
unfold cfg_at.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ0 SHOK Bsp.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK Bsp.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (YI08.U_not E 18 tab E18 ltac:(lia)), (s21_U_mul E 36 (x_cap cx) 18 E36 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ0 SHOK Bsp.
{ cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }


lazymatch goal with HEIx : img_env _ _ E |- _ => rename HEIx into HEIc end.
s21_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3076)) MRA ltac:(apply codeptr_val; exact HEIc).
s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) MSP ltac:(cbn [sv_denot]; rewrite E2, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) MGP ltac:(cbn [sv_denot]; rewrite E3, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) MTP ltac:(cbn [sv_denot]; rewrite E4, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) MS0 ltac:(cbn [sv_denot]; rewrite E8, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) MS1 ltac:(cbn [sv_denot]; rewrite E9, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
s21_reg HS (18%bv : bv 5) (w64 tab) MS2 ltac:(cbn [sv_denot]; rewrite E18, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
s21_reg HS (19%bv : bv 5) (w64 mt) MS3 ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (UA : sv_denot E (SAlu ALU_ADD (SOff 18 0) (SMd M_MUL (SOff 36 0) (SLit 18))) = w64 (tab + 18 * x_cap cx)).
{ rewrite denot_lit_U, U_SAlu, (U_atom E 18 tab E18 ltac:(lia)), (s21_U_mul E 36 (x_cap cx) 18 E36 ltac:(lia) ltac:(lia) ltac:(lia)).
  cbn [zalu_raw]. unfold zcanon, w64, M64. f_equal. rewrite Z.mod_small by lia. lia. }
s21_reg HS (10%bv : bv 5) (w64 (tab + 18 * x_cap cx)) MA0 ltac:(exact UA).
s21_reg HS (11%bv : bv 5) (w64 90) MA1 ltac:(reflexivity).
s21_reg HS (12%bv : bv 5) (w64 18) MA2 ltac:(reflexivity).
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ False -> rdW W (ms_mem ms) a = rdW W mem a)
  by (s21_kept HFr (fun _ : Z => False) ltac:(fun Hr => lia)).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ False -> rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a)
  by (s21_kept HFr0 (fun _ : Z => False) ltac:(fun Hr => lia)).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W mem a)
  by (intros a Ha; rewrite (K2 a Ha ltac:(tauto)); exact (K1 a Ha ltac:(tauto))).
clear K1 K2 HF HFr HG HF0 HFr0 HG0.


pose proof (proj1 HJ0) as HARc.
assert (Hspc : spZ (ms_regs ms0) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite MSP. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
assert (Hd : tab <= tab + 18 * x_cap cx /\ tab + 18 * x_cap cx + 18 <= tab + req_size (x_tabn cx)).
{ rewrite s21_req by lia. unfold x_tabn, seg_spec.RVLAN_SIZE. lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG SS___asan_memset) (AMEMSET fx)
    W (ms_regs ms0) (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (tab + 18 * x_cap cx) 90 18 (x_s1 cx - x_sp0 cx)
    (Z_to_bv 64 (BASE + 3076)) HJ0 MA0 MA1 MA2).
  all: try lia.
  - unfold ESTACK. lia.
  - exact MGP.
  - exact MTP.
  - exact MRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|unfold ESTACK; lia].
    right; right; left. exists tab, (x_tabn cx). split; [exact Hint|]. split; [|lia].
    exact (s21_notin_bl0 cx ly S W mem md _ _ HAR0 Hbl ltac:(right; left; reflexivity)).
  - intros a Ha HFP. exfalso. exact (s21_blk_off_fp ly S W mem md tab (x_tabn cx) a HAR0 Hint ltac:(lia) HFP).
  - eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hint); lia.
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hint); lia.
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hint); lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HSET & HKM & _ & _).
apply (HSTB cx ly S W regs mem md k acc c m tab mt regs2 mem2 md2 Hcut); [| exact HK0 | exact HKE].

split; [exact HJ2|]. split.
{ unfold s21_rg.
  split; [exact (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) MSP)|].
  split; [exact (eq_trans (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) MGP) (eq_sym Hgp))|].
  split; [exact (eq_trans (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) MTP) (eq_sym Htp))|].
  split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) MS0)|].
  exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) MS1). }
split; [exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) MS2)|].
split; [exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) MS3)|].
split.
{ intros a Ha Hs Hd'. rewrite (HKM a Ha Hd' ltac:(unfold ESTACK; lia)). exact (KR a Ha). }
intros i Hi. rewrite (HSET i Hi). reflexivity.
Qed.

(* ==================== stage B: 0x859c4 .. the flags / cap branches ==================== *)

Lemma s21_stB : (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  (Z.land (x_flags cx) 1 = 0 \/ x_cap cx = 0) -> LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsA (Z_to_bv 64 (BASE + 0xcc4)) memA (seg_rom SEGS)) mdA) (lt_post B MT cx)) -> (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 -> LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsA (Z_to_bv 64 (BASE + 0xc30)) memA (seg_rom SEGS)) mdA) (lt_post B MT cx)) -> forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsB memB mdB,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptB cx ly S W mem0 k tab mt regsB memB mdB ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsB (Z_to_bv 64 (BASE + 0xc04)) memB (seg_rom SEGS)) mdB) (lt_post B MT cx).
Proof.
intros HP0 HP1 cx ly S W regs0 mem0 md0 k acc c m tab mt regsB memB mdB Hcut HB HK0 HKE.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
destruct HB as (HJ & (R2 & R3 & R4 & R8 & R9) & R18 & R19 & KB & GB).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (KS : forall o v, 16 <= o <= 216 -> rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memB) (x_s1 cx + o) = Some v).
{ intros o v Ho Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros i Hi. apply KB; lia. }
pose proof (s21_seed2 0xc04 18 19 18%bv 19%bv 16 16 128 128 W regsB memB (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R9 R2 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) R18 ltac:(lia) Hta R19 ltac:(lia) Hmta
  (KS 32 _ ltac:(lia) S32) (KS 48 _ ltac:(lia) S48) (KS 56 _ ltac:(lia) S56) (KS 64 _ ltac:(lia) S64) (KS 176 _ ltac:(lia) S176)
  (KS 184 _ ltac:(lia) S184) (KS 192 _ ltac:(lia) S192) (KS 200 _ ltac:(lia) S200) (KS 216 _ ltac:(lia) S216)) as HS.


set (E := s21_E regsB (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr (x_fr cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 61)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (Hsfb2 : 2147446784 <= shadow_addr (x_fr cx) /\ shadow_addr (x_fr cx) + 64 <= 17594333495296)
  by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 44)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (apply BU; [unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl), R9; reflexivity | lia]).
assert (U33 : bv_unsigned (ew E 33) = x_fr cx) by exact (BU 33%nat _ (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl) ltac:(lia)).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (x_fr cx)) by exact (BU 34%nat _ (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl) Hsf).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & Hfpres2 & Hfshp2).
rewrite Efr in Hfpres2, Hfshp2. rewrite HF512 in Hfpres2, Hfshp2.
pose proof (st_ok_pi_add_region E _ _ s21_fsh HS eq_refl) as HS1.


assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R3; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R4; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 19 19%bv eq_refl); exact R19).

assert (RF : region_ok SEGS E (ms_mem (restrict (w_H W) (mkst regsB (Z_to_bv 64 (BASE + 3076)) memB (seg_rom SEGS)))) s21_fsh).
{ cbn [ms_mem restrict mkst]. unfold s21_fsh, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (shadow_addr (x_fr cx) + o) with (shadow_addr (x_fr cx) + 32) by lia.
  apply (Hfshp2 32 ltac:(lia)). }
specialize (HS1 RF). clear RF.
assert (DF : all_disjoint E s21_fsh (ss_mem (mkSS 3076 sr_atoms [s21_sl1 16 16; s21_sl2 128 128] None (s21_G 18 19)))).
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, s21_fsh, s21_sl1, s21_sl2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite U34, U9. lia. }
pose proof (HS1 DF) as HS2. clear HS1 DF. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.


pose proof (st_ok_pi_add_region E _ _ s21_frn HS2 eq_refl) as HS3.
assert (RN : region_ok SEGS E (ms_mem (restrict (w_H W) (mkst regsB (Z_to_bv 64 (BASE + 3076)) memB (seg_rom SEGS)))) s21_frn).
{ cbn [ms_mem restrict mkst]. unfold s21_frn, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hfpres2 (x_fr cx + o) ltac:(lia))). }
specialize (HS3 RN). clear RN.
assert (DN : all_disjoint E s21_frn (ss_mem (mkSS 3076 sr_atoms [s21_fsh; s21_sl1 16 16; s21_sl2 128 128] None (s21_G 18 19)))).
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, s21_fsh, s21_frn, s21_sl1, s21_sl2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite U33, U34, U9.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. lia. }
clear HS. pose proof (HS3 DN) as HS. clear HS2 HS3 DN. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (PaLibF.SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (PaLibF.SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (PI := PI)) as BR.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => x_fr cx + 256 <= x < x_fr cx + 260 \/ x = x_sh cx + 32) a -> rdW W memB a = rdW W memB a) by reflexivity.
PaLibF.paj_run_sh RUNP HS HJ.

{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 33%nat (x_fr cx)); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 34%nat (shadow_addr (x_fr cx))); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr. s21_fold KR (fun x => x_fr cx + 256 <= x < x_fr cx + 260 \/ x = x_sh cx + 32) ltac:(fun Hr => rewrite ?U33, ?U34, ?U9 in Hr; cbv beta; unfold x_sh; lia).

lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict (w_H W) ms) =>
  let r := eval vm_compute in (sym_step_pi seg_tpi ss) in
  lazymatch r with PStop (SR_branch ?cc ?aa ?bb) =>
    apply (BR W E ss ms _ _ cc aa bb HS); clear HS; intros Hc HS end end.


{ PaLibF.paj_run_to_sh RUNTOP HS HJ 0xcc4.
{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 33%nat (x_fr cx)); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 34%nat (shadow_addr (x_fr cx))); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s21_fold KR (fun x => x_fr cx + 256 <= x < x_fr cx + 260 \/ x = x_sh cx + 32) ltac:(fun Hr => rewrite ?U33, ?U34, ?U9 in Hr; cbv beta; unfold x_sh; lia).

  s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) A2 ltac:(apply s21_den0; exact E2).
  s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) A3 ltac:(apply s21_den0; exact E3).
  s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) A4 ltac:(apply s21_den0; exact E4).
  s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) A8 ltac:(apply s21_den0; exact E8).
  s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) A9 ltac:(apply s21_den0; exact E9).
  s21_reg HS (18%bv : bv 5) (w64 tab) A18 ltac:(apply s21_den0; exact E18).
  s21_reg HS (19%bv : bv 5) (w64 mt) A19 ltac:(apply s21_den0; exact E19).
  s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) A20 ltac:(apply s21_denc; [exact E19 | lia]).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s21_fsh) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
    assert (HR0 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r0)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity);
    assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity) end.
  cbn [ms_mem restrict] in HR0, HR1.
  pose proof (field_of_region E _ _ _ _ _ _ _ _ 256 4%N (SLit 0) 0 HR0 U33 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
  pose proof (field_of_region E _ _ _ _ _ _ _ _ 32 1%N (SLit 4) 4 HR1 U34 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS.
  clear HR0 HR1.
  pmkst HS.

  apply (HP0 cx ly S W regs0 mem0 md0 k acc c m tab mt _ _ _ Hcut); [| | exact HK0 | exact HKE].
  2: { left. rewrite branch_eq_U, U_SAlu, (U_atom E 37 (x_flags cx) (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl) Hflr), U_lit in Hc by lia.
       apply Z.eqb_eq in Hc. cbn [zalu_raw] in Hc. unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc; [exact Hc|].
       rewrite s21_land1. pose proof (Z.mod_pos_bound (x_flags cx) 2 ltac:(lia)). lia. }

  split; [exact HJ|]. split; [exact (conj A2 (conj (eq_trans A3 (eq_sym Hgp)) (conj (eq_trans A4 (eq_sym Htp)) (conj A8 A9))))|].
  split; [exact A18|]. split; [exact A19|]. split; [exact A20|].
  split.
  { intros a Ha H1 H2 H3 H4. rewrite (KR a Ha ltac:(cbv beta; tauto)). exact (KB a Ha H1 H2). }
  split.
  { intros i Hi. rewrite (KR (tab + 18 * x_cap cx + i) ltac:(lia) ltac:(cbv beta; intros [Hx|Hx]; [unfold zdisjoint in Dtf; cbn [fst snd] in Dtf; destruct Dtf as [Dtf|Dtf]; unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia | destruct Htapp as [_ [Ht1 | [Ht1 Ht2]]]; unfold kLowShadowBeg, kHighMemBeg, x_tabn, seg_spec.RVLAN_SIZE in *; lia])). exact (GB i Hi). }
  split; [exact (s21_val1 W _ _ _ VS ltac:(lia))|].
  exact (s21_sa_val_of_val_mem _ _ _ _ _ VN).
  }


{ 
  rename Hc into Hc1.
  assert (Hfl1 : Z.land (x_flags cx) 1 <> 0).
  { rewrite branch_eq_U, U_SAlu, (U_atom E 37 (x_flags cx) (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl) Hflr), U_lit in Hc1 by lia.
    apply Z.eqb_neq in Hc1. cbn [zalu_raw] in Hc1. unfold zcanon, M64 in Hc1. rewrite Z.mod_small in Hc1; [exact Hc1|].
    rewrite s21_land1. pose proof (Z.mod_pos_bound (x_flags cx) 2 ltac:(lia)). lia. }
  clear Hc1.

  PaLibF.paj_run_sh RUNP HS HJ.
{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 33%nat (x_fr cx)); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 34%nat (shadow_addr (x_fr cx))); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s21_fold KR (fun x => x_fr cx + 256 <= x < x_fr cx + 260 \/ x = x_sh cx + 32) ltac:(fun Hr => rewrite ?U33, ?U34, ?U9 in Hr; cbv beta; unfold x_sh; lia).

  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict (w_H W) ms0) =>
    let r := eval vm_compute in (sym_step_pi seg_tpi ss) in
    lazymatch r with PStop (SR_branch ?cc ?aa ?bb) =>
      apply (BR W E ss ms0 _ _ cc aa bb HS); clear HS; intros Hc HS end end.
  

  { PaLibF.paj_run_to_sh RUNTOP HS HJ 0xcc4.
{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 33%nat (x_fr cx)); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 34%nat (shadow_addr (x_fr cx))); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    s21_fold KR (fun x => x_fr cx + 256 <= x < x_fr cx + 260 \/ x = x_sh cx + 32) ltac:(fun Hr => rewrite ?U33, ?U34, ?U9 in Hr; cbv beta; unfold x_sh; lia).

  s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) A2 ltac:(apply s21_den0; exact E2).
  s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) A3 ltac:(apply s21_den0; exact E3).
  s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) A4 ltac:(apply s21_den0; exact E4).
  s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) A8 ltac:(apply s21_den0; exact E8).
  s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) A9 ltac:(apply s21_den0; exact E9).
  s21_reg HS (18%bv : bv 5) (w64 tab) A18 ltac:(apply s21_den0; exact E18).
  s21_reg HS (19%bv : bv 5) (w64 mt) A19 ltac:(apply s21_den0; exact E19).
  s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) A20 ltac:(apply s21_denc; [exact E19 | lia]).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s21_fsh) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
    assert (HR0 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r0)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity);
    assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity) end.
  cbn [ms_mem restrict] in HR0, HR1.
  pose proof (field_of_region E _ _ _ _ _ _ _ _ 256 4%N (SLit 0) 0 HR0 U33 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
  pose proof (field_of_region E _ _ _ _ _ _ _ _ 32 1%N (SLit 4) 4 HR1 U34 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS.
  clear HR0 HR1.
  pmkst HS.

    apply (HP0 cx ly S W regs0 mem0 md0 k acc c m tab mt _ _ _ Hcut); [| | exact HK0 | exact HKE].
    2: { right. rewrite branch_eq_U, (U_atom E 36 (x_cap cx) (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl) ltac:(lia)), U_lit in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }

  split; [exact HJ|]. split; [exact (conj A2 (conj (eq_trans A3 (eq_sym Hgp)) (conj (eq_trans A4 (eq_sym Htp)) (conj A8 A9))))|].
  split; [exact A18|]. split; [exact A19|]. split; [exact A20|].
  split.
  { intros a Ha H1 H2 H3 H4. rewrite (KR a Ha ltac:(cbv beta; tauto)). exact (KB a Ha H1 H2). }
  split.
  { intros i Hi. rewrite (KR (tab + 18 * x_cap cx + i) ltac:(lia) ltac:(cbv beta; intros [Hx|Hx]; [unfold zdisjoint in Dtf; cbn [fst snd] in Dtf; destruct Dtf as [Dtf|Dtf]; unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia | destruct Htapp as [_ [Ht1 | [Ht1 Ht2]]]; unfold kLowShadowBeg, kHighMemBeg, x_tabn, seg_spec.RVLAN_SIZE in *; lia])). exact (GB i Hi). }
  split; [exact (s21_val1 W _ _ _ VS ltac:(lia))|].
  exact (s21_sa_val_of_val_mem _ _ _ _ _ VN).
  }
  { assert (Hcap0 : x_cap cx <> 0).
    { rewrite branch_eq_U, (U_atom E 36 (x_cap cx) (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl) ltac:(lia)), U_lit in Hc by lia. apply Z.eqb_neq in Hc; exact Hc. }
    PaLibF.paj_run_to_sh RUNTOP HS HJ 0xc30.
{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 33%nat (x_fr cx)); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 34%nat (shadow_addr (x_fr cx))); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [s21_frn s21_fsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    s21_fold KR (fun x => x_fr cx + 256 <= x < x_fr cx + 260 \/ x = x_sh cx + 32) ltac:(fun Hr => rewrite ?U33, ?U34, ?U9 in Hr; cbv beta; unfold x_sh; lia).

  s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) A2 ltac:(apply s21_den0; exact E2).
  s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) A3 ltac:(apply s21_den0; exact E3).
  s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) A4 ltac:(apply s21_den0; exact E4).
  s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) A8 ltac:(apply s21_den0; exact E8).
  s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) A9 ltac:(apply s21_den0; exact E9).
  s21_reg HS (18%bv : bv 5) (w64 tab) A18 ltac:(apply s21_den0; exact E18).
  s21_reg HS (19%bv : bv 5) (w64 mt) A19 ltac:(apply s21_den0; exact E19).
  s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) A20 ltac:(apply s21_denc; [exact E19 | lia]).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s21_fsh) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
    assert (HR0 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r0)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity);
    assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity) end.
  cbn [ms_mem restrict] in HR0, HR1.
  pose proof (field_of_region E _ _ _ _ _ _ _ _ 256 4%N (SLit 0) 0 HR0 U33 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
  pose proof (field_of_region E _ _ _ _ _ _ _ _ 32 1%N (SLit 4) 4 HR1 U34 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS.
  clear HR0 HR1.
  pmkst HS.

    apply (HP1 cx ly S W regs0 mem0 md0 k acc c m tab mt _ _ _ Hcut); [| exact Hfl1 | exact Hcap0 | exact HK0 | exact HKE].

  split; [exact HJ|]. split; [exact (conj A2 (conj (eq_trans A3 (eq_sym Hgp)) (conj (eq_trans A4 (eq_sym Htp)) (conj A8 A9))))|].
  split; [exact A18|]. split; [exact A19|]. split; [exact A20|].
  split.
  { intros a Ha H1 H2 H3 H4. rewrite (KR a Ha ltac:(cbv beta; tauto)). exact (KB a Ha H1 H2). }
  split.
  { intros i Hi. rewrite (KR (tab + 18 * x_cap cx + i) ltac:(lia) ltac:(cbv beta; intros [Hx|Hx]; [unfold zdisjoint in Dtf; cbn [fst snd] in Dtf; destruct Dtf as [Dtf|Dtf]; unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia | destruct Htapp as [_ [Ht1 | [Ht1 Ht2]]]; unfold kLowShadowBeg, kHighMemBeg, x_tabn, seg_spec.RVLAN_SIZE in *; lia])). exact (GB i Hi). }
  split; [exact (s21_val1 W _ _ _ VS ltac:(lia))|].
  exact (s21_sa_val_of_val_mem _ _ _ _ _ VN).
  }
}
Qed.

(* ==================== no seed (0x85a84 .. 0x85a98) ==================== *)

Lemma s21_P0 : (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsJ memJ mdJ,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptJ cx ly S W mem0 k tab mt regsJ memJ mdJ ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsJ (Z_to_bv 64 (BASE + 0xcd8)) memJ (seg_rom SEGS)) mdJ) (lt_post B MT cx)) -> forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  (Z.land (x_flags cx) 1 = 0 \/ x_cap cx = 0) -> LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsA (Z_to_bv 64 (BASE + 0xcc4)) memA (seg_rom SEGS)) mdA) (lt_post B MT cx).
Proof.
intros HJT cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA Hcut HA Hcond HK0 HKE.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
destruct HA as (HJ & (R2 & R3 & R4 & R8 & R9) & R18 & R19 & R20 & KA & GA & SA & NA).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (KS : forall o v, 16 <= o <= 216 -> rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memA) (x_s1 cx + o) = Some v).
{ intros o v Ho Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros i Hi. apply KA; unfold x_sh in *; lia. }
pose proof (s21_seed2 0xcc4 18 19 18%bv 19%bv 16 16 128 168 W regsA memA (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R9 R2 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) R18 ltac:(lia) Hta R19 ltac:(lia) Hmta
  (KS 32 _ ltac:(lia) S32) (KS 48 _ ltac:(lia) S48) (KS 56 _ ltac:(lia) S56) (KS 64 _ ltac:(lia) S64) (KS 176 _ ltac:(lia) S176)
  (KS 184 _ ltac:(lia) S184) (KS 192 _ ltac:(lia) S192) (KS 200 _ ltac:(lia) S200) (KS 216 _ ltac:(lia) S216)) as HS.


set (E := s21_E regsA (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr (x_fr cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 61)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R3; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R4; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (s21_E_x _ _ _ _ _ _ _ 0 _ ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (x_fr cx)) by exact (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (x_fr cx))) by exact (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 m) by exact (s21_E_x _ _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (x_cap cx)) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (x_flags cx)) by exact (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (apply BU; [exact E9 | lia]).
assert (U18 : bv_unsigned (ew E 18) = tab) by (apply BU; [exact E18 | lia]).
assert (U19 : bv_unsigned (ew E 19) = mt) by (apply BU; [exact E19 | lia]).
assert (U33 : bv_unsigned (ew E 33) = x_fr cx) by (apply BU; [exact E33 | lia]).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (x_fr cx)) by (apply BU; [exact E34 | exact Hsf]).
assert (U35 : bv_unsigned (ew E 35) = m) by (apply BU; [exact E35 | lia]).

pose proof (PaLibF.SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (PaLibF.SRr_run_to_pi_AJ B LAWS) as RUNTOP.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168) a -> rdW W memA a = rdW W memA a) by reflexivity.
PaLibF.paj_run_to_sh RUNTOP HS HJ 0xcd8.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | ]. apply awr_ok_nil. }

cbn [ms_mem mkst] in HFr. s21_fold KR (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168) ltac:(fun Hr => rewrite ?U9 in Hr; cbv beta; lia).

assert (T0 : x_tab0 cx = []).
{ rewrite s21_tab0. destruct Hcond as [Hc | Hc]; rewrite Hc; [reflexivity|]. rewrite andb_false_r. reflexivity. }
s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) A2 ltac:(apply s21_den0; exact E2).
s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) A3 ltac:(apply s21_den0; exact E3).
s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) A4 ltac:(apply s21_den0; exact E4).
s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) A8 ltac:(apply s21_den0; exact E8).
s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) A9 ltac:(apply s21_den0; exact E9).
s21_reg HS (16%bv : bv 5) (w64 SHADOW_OFF) A16 ltac:(apply s21_den0; exact E32).
s21_reg HS (18%bv : bv 5) (w64 tab) A18 ltac:(apply s21_den0; exact E18).
s21_reg HS (19%bv : bv 5) (w64 mt) A19 ltac:(apply s21_den0; exact E19).
assert (E20 : ew E 20 = w64 (mt + 16)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 20 20%bv eq_refl); exact R20).
s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) A20 ltac:(apply s21_den0; exact E20).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
  assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
    by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity) end.
cbn [ms_mem restrict] in HR1.
pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region E _ _ _ _ _ _ _ _ 128 8%N (SLit 0) 0 HR1 U9 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as J128.
pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region E _ _ _ _ _ _ _ _ 160 8%N (SLit 1) 1 HR1 U9 ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as J160.
clear HR1.
pmkst HS.
apply (HJT cx ly S W regs0 mem0 md0 k acc c m tab mt _ _ _ Hcut); [| exact HK0 | exact HKE].
assert (KJ : forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rdW W (ms_mem ms) a = rdW W mem0 a).
{ intros a Ha Hn. unfold s21_ws in Hn. rewrite (KR a Ha ltac:(cbv beta; lia)).
  apply KA; [exact Ha | lia | unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia | lia | lia]. }
assert (KJA : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 128 <= a < x_s1 cx + 168) -> rdW W (ms_mem ms) a = rdW W memA a)
  by (intros a Ha Hn; exact (KR a Ha ltac:(cbv beta; lia))).
split; [exact HJ|]. split; [exact (conj A2 (conj (eq_trans A3 (eq_sym Hgp)) (conj (eq_trans A4 (eq_sym Htp)) (conj A8 A9))))|].
split; [exact A16|]. split; [exact A18|]. split; [exact A19|]. split; [exact A20|].
split; [exact KJ|].
rewrite T0. cbn [length Z.of_nat].
split; [exact J128|]. split; [exact J160|].
split; [rewrite (KJA (x_sh cx + 32) ltac:(lia) ltac:(lia)); exact SA|].
split; [intros kk Hk; rewrite (KJA (x_fr cx + FO_N + Z.of_nat kk) ltac:(unfold FO_N; lia) ltac:(unfold FO_N; lia)); exact (NA kk Hk)|].
split; [apply s21_rtab_nil|]. split; [|apply s21_mtab_nil].
apply s21_guard. intros i Hi. rewrite (KJA (tab + 18 * x_cap cx + i) ltac:(lia) ltac:(lia)). exact (GA i Hi).
Qed.

(* ==================== the seed: memcpy into tab (0x859f0 .. 0x85a08) ==================== *)

Lemma s21_P1a : (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regsX memX mdX,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 -> s21_q1 cx ly S W k tab mt memA regsX memX mdX ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (BASE + 0xc4c)) memX (seg_rom SEGS)) mdX) (lt_post B MT cx)) -> forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 -> LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsA (Z_to_bv 64 (BASE + 0xc30)) memA (seg_rom SEGS)) mdA) (lt_post B MT cx).
Proof.
intros HQ1 cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA Hcut HA Hfl1 Hcap0 HK0 HKE.
pose proof HA as HA0.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
destruct HA as (HJ & (R2 & R3 & R4 & R8 & R9) & R18 & R19 & R20 & KA & GA & SA & NA).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (KS : forall o v, 16 <= o <= 216 -> rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memA) (x_s1 cx + o) = Some v).
{ intros o v Ho Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros i Hi. apply KA; unfold x_sh in *; lia. }
pose proof (s21_seed2 0xc30 18 19 18%bv 19%bv 16 16 128 128 W regsA memA (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R9 R2 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) R18 ltac:(lia) Hta R19 ltac:(lia) Hmta
  (KS 32 _ ltac:(lia) S32) (KS 48 _ ltac:(lia) S48) (KS 56 _ ltac:(lia) S56) (KS 64 _ ltac:(lia) S64) (KS 176 _ ltac:(lia) S176)
  (KS 184 _ ltac:(lia) S184) (KS 192 _ ltac:(lia) S192) (KS 200 _ ltac:(lia) S200) (KS 216 _ ltac:(lia) S216)) as HS.

set (E := s21_E regsA (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr (x_fr cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 61)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R3; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R4; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (s21_E_x _ _ _ _ _ _ _ 0 _ ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (x_fr cx)) by exact (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (x_fr cx))) by exact (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 m) by exact (s21_E_x _ _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (x_cap cx)) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (x_flags cx)) by exact (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (apply BU; [exact E9 | lia]).
assert (U18 : bv_unsigned (ew E 18) = tab) by (apply BU; [exact E18 | lia]).
assert (U19 : bv_unsigned (ew E 19) = mt) by (apply BU; [exact E19 | lia]).
assert (U33 : bv_unsigned (ew E 33) = x_fr cx) by (apply BU; [exact E33 | lia]).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (x_fr cx)) by (apply BU; [exact E34 | exact Hsf]).
assert (U35 : bv_unsigned (ew E 35) = m) by (apply BU; [exact E35 | lia]).

assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) memA)) by constructor.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.


assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> rdW W memA a = rdW W memA a) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bsp.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr. s21_fold KR (fun _ : Z => False) ltac:(fun Hr => lia).


assert (E20 : ew E 20 = w64 (mt + 16)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 20 20%bv eq_refl); exact R20).
assert (E250 : ew E 250 = w64 0x21060).
{ unfold E, s21_E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
  change 250%nat with (A_OBJ 9). rewrite (VOBJS 9%nat (proj2 (proj2 s21_lit_enp_addr))), (proj1 (proj2 s21_lit_enp_addr)). reflexivity. }
lazymatch goal with HEIx : img_env _ _ E |- _ => rename HEIx into HEIc end.
s21_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3148)) MRA ltac:(apply codeptr_val; exact HEIc).
s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) MSP ltac:(apply s21_den0; exact E2).
s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) MGP ltac:(apply s21_den0; exact E3).
s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) MTP ltac:(apply s21_den0; exact E4).
s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) MS0 ltac:(apply s21_den0; exact E8).
s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) MS1 ltac:(apply s21_den0; exact E9).
s21_reg HS (18%bv : bv 5) (w64 tab) MS2 ltac:(apply s21_den0; exact E18).
s21_reg HS (19%bv : bv 5) (w64 mt) MS3 ltac:(apply s21_den0; exact E19).
s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) MS4 ltac:(apply s21_den0; exact E20).
s21_reg HS (10%bv : bv 5) (w64 tab) MA0 ltac:(apply s21_den0; exact E18).
s21_reg HS (11%bv : bv 5) (w64 0x21060) MA1 ltac:(apply s21_den0; exact E250).
s21_reg HS (12%bv : bv 5) (w64 7) MA2 ltac:(reflexivity).
pose proof (proj1 HJ) as HARc.
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ot & Omt & Of & _).
unfold off_img in Ot, Omt, Of.
assert (LZ : sa_zs (rdW W (ms_mem ms)) 0x21060 (SegModel.S_enp ++ [0])).
{ apply (s21_zs_keep (rdW W mem0)); [|exact (s21_lit_zs cx _ Himg)].
  intros i Hi. change (Z.of_nat (length (SegModel.S_enp ++ [0]))) with 7 in Hi.
  rewrite (KR (0x21060 + i) ltac:(lia) ltac:(cbv beta; tauto)).
  apply KA; [lia | lia | destruct Ot; lia | destruct Of; lia | unfold x_sh in *; lia]. }
assert (Hspc : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite MSP. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
pmkst HS.


eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx)
    W (ms_regs ms) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ _ _ _ tab 0x21060 7 (x_s1 cx - x_sp0 cx)
    (Z_to_bv 64 (BASE + 3148)) HJ MA0 MA1 MA2).
  all: try lia.
  - unfold ESTACK. lia.
  - exact MGP.
  - exact MTP.
  - exact MRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|unfold ESTACK; lia].
    right; right; left. exists tab, (x_tabn cx). split; [exact Hint|]. split; [|rewrite s21_req by lia; lia].
    exact (s21_notin_bl0 cx ly S W mem0 md0 _ _ HAR0 Hbl ltac:(right; left; reflexivity)).
  - intros a Ha HFP. exfalso. exact (s21_blk_off_fp ly S W mem0 md0 tab (x_tabn cx) a HAR0 Hint ltac:(rewrite s21_req; lia) HFP).
  - eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hint); rewrite ?s21_req; lia.
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hint); rewrite ?s21_req; lia.
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hint); rewrite ?s21_req; lia.
  - destruct (s21_lit_addr cx _ ly S W _ _ Himg HARc) as (LA0 & LA1 & LA2 & LA3 & LA4).
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - pose proof (LZ (Z.to_nat (a - 0x21060)) ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat; lia)) as Hb.
        rewrite Z2Nat.id in Hb by lia. replace (0x21060 + (a - 0x21060)) with a in Hb by lia. rewrite Hb. discriminate.
      - rewrite Hspc. unfold ESTACK. lia. }
    split; [destruct Ot; lia|]. split; [exact LA2|]. split; [exact LA3|]. exact LA4. }


cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HCPY & HKM & _ & _).
apply (HQ1 cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regs2 mem2 md2 Hcut HA0 Hfl1 Hcap0); [| exact HK0 | exact HKE].
split; [exact HJ2|]. split.
{ unfold s21_rg.
  split; [exact (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) MSP)|].
  split; [exact (eq_trans (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) MGP) (eq_sym Hgp))|].
  split; [exact (eq_trans (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) MTP) (eq_sym Htp))|].
  split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) MS0)|].
  exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) MS1). }
split; [exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) MS2)|].
split; [exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) MS3)|].
split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) MS4)|].
split.
{ intros a Ha Hs Ht. rewrite (HKM a Ha Ht ltac:(unfold ESTACK; lia)). exact (KR a Ha ltac:(cbv beta; tauto)). }
intros i Hi. rewrite (HCPY (Z.of_nat i) ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat in Hi; lia)). exact (LZ i Hi).
Qed.

(* ==================== the seed: tab's VLAN, memcpy into mt (0x85a0c .. 0x85a44) ==================== *)

Lemma s21_P1b : (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regsY memY mdY,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 -> s21_q2 cx ly S W k tab mt memA regsY memY mdY ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsY (Z_to_bv 64 (BASE + 0xc88)) memY (seg_rom SEGS)) mdY) (lt_post B MT cx)) -> forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regsX memX mdX,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 -> s21_q1 cx ly S W k tab mt memA regsX memX mdX ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (BASE + 0xc4c)) memX (seg_rom SEGS)) mdX) (lt_post B MT cx).
Proof.
intros HQ2 cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regsX memX mdX Hcut HA Hfl1 Hcap0 HQ HK0 HKE.
pose proof HA as HA0. pose proof Hcut as Hcut0. s21_unpack Hcut0.
destruct HA as (_ & _ & _ & _ & _ & KA & GA & SA & NA).
destruct HQ as (HJ & (R2 & R3 & R4 & R8 & R9) & R18 & R19 & R20 & KX & ZT).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ot & Omt & Of & _).
unfold off_img in Ot, Omt, Of.
assert (KS : forall o v, 16 <= o <= 216 -> rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memX) (x_s1 cx + o) = Some v).
{ intros o v Ho Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros i Hi.
  rewrite KX by (unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia). apply KA; unfold x_sh, x_tabn, seg_spec.RVLAN_SIZE in *; lia. }
pose proof (s21_seed2 0xc4c 18 19 18%bv 19%bv 16 16 128 128 W regsX memX (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R9 R2 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) R18 ltac:(lia) Hta R19 ltac:(lia) Hmta
  (KS 32 _ ltac:(lia) S32) (KS 48 _ ltac:(lia) S48) (KS 56 _ ltac:(lia) S56) (KS 64 _ ltac:(lia) S64) (KS 176 _ ltac:(lia) S176)
  (KS 184 _ ltac:(lia) S184) (KS 192 _ ltac:(lia) S192) (KS 200 _ ltac:(lia) S200) (KS 216 _ ltac:(lia) S216)) as HS.

set (E := s21_E regsX (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr (x_fr cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 61)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R3; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R4; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (s21_E_x _ _ _ _ _ _ _ 0 _ ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (x_fr cx)) by exact (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (x_fr cx))) by exact (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 m) by exact (s21_E_x _ _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (x_cap cx)) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (x_flags cx)) by exact (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (apply BU; [exact E9 | lia]).
assert (U18 : bv_unsigned (ew E 18) = tab) by (apply BU; [exact E18 | lia]).
assert (U19 : bv_unsigned (ew E 19) = mt) by (apply BU; [exact E19 | lia]).
assert (U33 : bv_unsigned (ew E 33) = x_fr cx) by (apply BU; [exact E33 | lia]).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (x_fr cx)) by (apply BU; [exact E34 | exact Hsf]).
assert (U35 : bv_unsigned (ew E 35) = m) by (apply BU; [exact E35 | lia]).

assert (E20 : ew E 20 = w64 (mt + 16)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 20 20%bv eq_refl); exact R20).


assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) memX)) by constructor.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> rdW W memX a = rdW W memX a) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bsp.


{ cbn [ms_mem mkst].
  rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)), (U_atom_off E 18 tab 16 ltac:(exact E18) ltac:(lia) ltac:(lia)).
  change (rd_of SEGS (mrestrict (w_H W) memX)) with (rdW W memX).
  eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hint); rewrite ?s21_req by lia; unfold x_tabn, seg_spec.RVLAN_SIZE; lia. }
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr. s21_fold KR (fun _ : Z => False) ltac:(fun Hr => lia).

lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in * end.
assert (EX : forall n, (n < 1024)%nat -> ew E' n = ew E n) by (intros nn Hnn; unfold E'; rewrite !ew_ewset_other by lia; reflexivity).
assert (U18' : bv_unsigned (ew E' 18) = tab) by (rewrite EX by lia; exact U18).
assert (U9' : bv_unsigned (ew E' 9) = x_s1 cx) by (rewrite EX by lia; exact U9).
pose proof (proj1 HJ) as HARs.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARs Hint) as (_ & _ & _ & _ & HtpresS & _).
pose proof (st_ok_pi_add_region E' _ _ s21_tb HS eq_refl) as HS1.
lazymatch type of HS1 with region_ok _ _ ?mm _ -> _ =>
  assert (RT : region_ok SEGS E' mm s21_tb) end.
{ cbn [ms_mem restrict mkst]. unfold s21_tb, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18'.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HtpresS (tab + o) ltac:(rewrite s21_req by lia; unfold x_tabn, seg_spec.RVLAN_SIZE; lia))). }
specialize (HS1 RT). clear RT.
lazymatch type of HS1 with all_disjoint _ _ ?l -> _ => assert (DT : all_disjoint E' s21_tb l) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, s21_tb, s21_sl1, s21_sl2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite U18', U9'. lia. }

clear HS. pose proof (HS1 DT) as HS. clear HS1 DT. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.


pose proof (PaLibF.SRr_run_to_pi_AJ B LAWS) as RUNTOP.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => tab + 16 <= x < tab + 18) a -> rdW W (ms_mem ms) a = rdW W memX a)
  by (intros a Ha _; exact (KR a Ha ltac:(cbv beta; tauto))).
clear KR. rename KR2 into KR.
PaLibF.paj_run_to_sh RUNTOP HS HJ 0xc84.
{ cbn [ss_mem].
  eapply (awr_ok_cons_gen B E' _ _ _ _ _ _ _ _ _ _ 18%nat tab); [reflexivity | exact U18' | |].
  { intros a Ha. cbn [s21_tb YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
    exists tab, (x_tabn cx). split; [exact Hint|]. split; [|rewrite s21_req by lia; unfold x_tabn, seg_spec.RVLAN_SIZE; lia].
    exact (s21_notin_bl0 cx ly S W mem0 md0 _ _ HAR0 Hbl ltac:(right; left; reflexivity)). }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }



s21_fold KR (fun x => tab + 16 <= x < tab + 18) ltac:(fun Hr => rewrite ?EX in Hr by lia; rewrite ?U18 in Hr; cbv beta; lia).

lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s21_fsh) in
  assert (HR0 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r0)
    by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity) end.
cbn [ms_mem restrict] in HR0.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 16 2%N (SLit 33) 33 HR0 U18' ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V16.
assert (B16 : rdW W (ms_mem ms0) (tab + 16) = Some 33).
{ pose proof (s21_aview_of_val_mem SEGS (w_H W) (ms_mem ms0) (tab + 16) 2 33 0 V16 ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
assert (B17 : rdW W (ms_mem ms0) (tab + 17) = Some 0).
{ pose proof (s21_aview_of_val_mem SEGS (w_H W) (ms_mem ms0) (tab + 16) 2 33 1 V16 ltac:(lia)) as H.
  replace (tab + 16 + Z.of_nat 1) with (tab + 17) in H by lia. exact H. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s21_fsh) in
  pose proof (PaLibF.ast_ok_pi_set_region Ex ssx (restrict Hh msx) 0 r0 (PaLibF.set_window r0 16 16) HS eq_refl eq_refl
    ltac:(vm_compute; reflexivity) (PaLibF.region_ok_rewindow SEGS Ex _ r0 16 16 HR0 ltac:(intros o Ho; lia))) as HS1 end.
clear HS HR0. rename HS1 into HS. cbv [PaLibF.list_upd PaLibF.set_window] in HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts YP09.r_base YP09.r_lo YP09.r_hi YP09.r_chunks] in HS.


clear SHOK. assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E' (mrestrict (w_H W) (ms_mem ms0))) by constructor.
rename KR into KRX.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> rdW W (ms_mem ms0) a = rdW W (ms_mem ms0) a) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bsp.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr. s21_fold KR (fun _ : Z => False) ltac:(fun Hr => lia).

assert (E250 : ew E' 250 = w64 0x21060).
{ rewrite EX by lia. unfold E, s21_E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
  change 250%nat with (A_OBJ 9). rewrite (VOBJS 9%nat (proj2 (proj2 s21_lit_enp_addr))), (proj1 (proj2 s21_lit_enp_addr)). reflexivity. }
assert (HEIc : img_env VAL A_LIM E') by assumption.
s21_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3208)) MRA ltac:(apply codeptr_val; exact HEIc).
s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) MSP ltac:(apply s21_den0; rewrite EX by lia; exact E2).
s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) MGP ltac:(apply s21_den0; rewrite EX by lia; exact E3).
s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) MTP ltac:(apply s21_den0; rewrite EX by lia; exact E4).
s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) MS0 ltac:(apply s21_den0; rewrite EX by lia; exact E8).
s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) MS1 ltac:(apply s21_den0; rewrite EX by lia; exact E9).
s21_reg HS (18%bv : bv 5) (w64 tab) MS2 ltac:(apply s21_den0; rewrite EX by lia; exact E18).
s21_reg HS (19%bv : bv 5) (w64 mt) MS3 ltac:(apply s21_den0; rewrite EX by lia; exact E19).
s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) MS4 ltac:(apply s21_den0; rewrite EX by lia; exact E20).
s21_reg HS (10%bv : bv 5) (w64 mt) MA0 ltac:(apply s21_den0; rewrite EX by lia; exact E19).
s21_reg HS (11%bv : bv 5) (w64 0x21060) MA1 ltac:(apply s21_den0; exact E250).
s21_reg HS (12%bv : bv 5) (w64 7) MA2 ltac:(reflexivity).
pose proof (proj1 HJ) as HARc.
assert (LZ : sa_zs (rdW W (ms_mem ms1)) 0x21060 (SegModel.S_enp ++ [0])).
{ apply (s21_zs_keep (rdW W mem0)); [|exact (s21_lit_zs cx _ Himg)].
  intros i Hi. change (Z.of_nat (length (SegModel.S_enp ++ [0]))) with 7 in Hi.
  rewrite (KR (0x21060 + i) ltac:(lia) ltac:(cbv beta; tauto)).
  rewrite (KRX (0x21060 + i) ltac:(lia) ltac:(cbv beta; destruct Ot; unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia)).
  rewrite (KX (0x21060 + i) ltac:(lia) ltac:(lia) ltac:(destruct Ot; unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia)).
  apply KA; [lia | lia | destruct Ot; lia | destruct Of; lia | unfold x_sh in *; lia]. }
assert (Hspc : spZ (ms_regs ms1) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite MSP. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx)
    W (ms_regs ms1) (ms_mem ms1) _ _ _ _ _ _ _ _ _ _ _ _ _ mt 0x21060 7 (x_s1 cx - x_sp0 cx)
    (Z_to_bv 64 (BASE + 3208)) HJ MA0 MA1 MA2).
  all: try lia.
  - unfold ESTACK. lia.
  - exact MGP.
  - exact MTP.
  - exact MRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|unfold ESTACK; lia].
    right; right; left. exists mt, (x_mtn cx). split; [exact Hinmt|]. split; [|rewrite s21_req by lia; unfold x_mtn, seg_spec.MVLAN_SIZE in *; lia].
    exact (s21_notin_bl0 cx ly S W mem0 md0 _ _ HAR0 Hbl ltac:(left; reflexivity)).
  - intros a Ha HFP. exfalso. exact (s21_blk_off_fp ly S W mem0 md0 mt (x_mtn cx) a HAR0 Hinmt ltac:(rewrite s21_req; unfold x_mtn, seg_spec.MVLAN_SIZE in *; lia) HFP).
  - eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hinmt); rewrite ?s21_req; unfold x_mtn, seg_spec.MVLAN_SIZE in *; lia.
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hinmt); rewrite ?s21_req; unfold x_mtn, seg_spec.MVLAN_SIZE in *; lia.
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hinmt); rewrite ?s21_req; unfold x_mtn, seg_spec.MVLAN_SIZE in *; lia.
  - destruct (s21_lit_addr cx _ ly S W _ _ Himg HARc) as (LA0 & LA1 & LA2 & LA3 & LA4).
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - pose proof (LZ (Z.to_nat (a - 0x21060)) ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat; lia)) as Hb.
        rewrite Z2Nat.id in Hb by lia. replace (0x21060 + (a - 0x21060)) with a in Hb by lia. rewrite Hb. discriminate.
      - rewrite Hspc. unfold ESTACK. lia. }
    split; [destruct Omt; unfold x_mtn, seg_spec.MVLAN_SIZE in *; lia|]. split; [exact LA2|]. split; [exact LA3|]. exact LA4. }


cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HCPY & HKM & _ & _).
apply (HQ2 cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regs2 mem2 md2 Hcut HA0 Hfl1 Hcap0); [| exact HK0 | exact HKE].
assert (KY1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) -> ~ (mt <= a < mt + 7) ->
  rdW W mem2 a = rdW W (ms_mem ms0) a).
{ intros a Ha Hs Hm. rewrite (HKM a Ha Hm ltac:(unfold ESTACK; lia)). exact (KR a Ha ltac:(cbv beta; tauto)). }
split; [exact HJ2|]. split.
{ unfold s21_rg.
  split; [exact (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) MSP)|].
  split; [exact (eq_trans (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) MGP) (eq_sym Hgp))|].
  split; [exact (eq_trans (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) MTP) (eq_sym Htp))|].
  split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) MS0)|].
  exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) MS1). }
split; [exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) MS2)|].
split; [exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) MS3)|].
split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) MS4)|].
split.
{ intros a Ha Hs Ht Ht16 Hm. rewrite (KY1 a Ha Hs Hm). rewrite (KRX a Ha ltac:(cbv beta; tauto)). exact (KX a Ha Hs Ht). }
split.
{ intros i Hi. change (length (SegModel.S_enp ++ [0])) with 7%nat in Hi.
  rewrite (KY1 (tab + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(unfold zdisjoint in Dtmt; cbn [fst snd] in Dtmt; unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in *; lia)).
  rewrite (KRX (tab + Z.of_nat i) ltac:(lia) ltac:(cbv beta; lia)).
  exact (ZT i ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat; lia)). }
split.
{ rewrite (KY1 (tab + 16) ltac:(lia) ltac:(lia) ltac:(unfold zdisjoint in Dtmt; cbn [fst snd] in Dtmt; unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in *; lia)). exact B16. }
split.
{ rewrite (KY1 (tab + 17) ltac:(lia) ltac:(lia) ltac:(unfold zdisjoint in Dtmt; cbn [fst snd] in Dtmt; unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in *; lia)). exact B17. }
intros i Hi. rewrite (HCPY (Z.of_nat i) ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat in Hi; lia)). exact (LZ i Hi).
Qed.

(* ==================== the seed: mt's VLAN, n := 1 (0x85a48 .. 0x85a80) ==================== *)

Lemma s21_P1c : (forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsJ memJ mdJ,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptJ cx ly S W mem0 k tab mt regsJ memJ mdJ ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsJ (Z_to_bv 64 (BASE + 0xcd8)) memJ (seg_rom SEGS)) mdJ) (lt_post B MT cx)) -> forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regsY memY mdY,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptA cx ly S W mem0 k tab mt regsA memA mdA ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 -> s21_q2 cx ly S W k tab mt memA regsY memY mdY ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsY (Z_to_bv 64 (BASE + 0xc88)) memY (seg_rom SEGS)) mdY) (lt_post B MT cx).
Proof.
intros HJT cx ly S W regs0 mem0 md0 k acc c m tab mt regsA memA mdA regsY memY mdY Hcut HA Hfl1 Hcap0 HQ HK0 HKE.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
destruct HA as (_ & _ & _ & _ & _ & KA & GA & SA & NA).
destruct HQ as (HJ & (R2 & R3 & R4 & R8 & R9) & R18 & R19 & R20 & KY & ZT & B16 & B17 & ZM).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (KS : forall o v, 16 <= o <= 216 -> rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memY) (x_s1 cx + o) = Some v).
{ intros o v Ho Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros i Hi.
  rewrite KY by (unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in *; lia). apply KA; unfold x_sh, x_tabn, seg_spec.RVLAN_SIZE in *; lia. }
pose proof (s21_seed2 0xc88 18 19 18%bv 19%bv 16 16 128 168 W regsY memY (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R9 R2 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) R18 ltac:(lia) Hta R19 ltac:(lia) Hmta
  (KS 32 _ ltac:(lia) S32) (KS 48 _ ltac:(lia) S48) (KS 56 _ ltac:(lia) S56) (KS 64 _ ltac:(lia) S64) (KS 176 _ ltac:(lia) S176)
  (KS 184 _ ltac:(lia) S184) (KS 192 _ ltac:(lia) S192) (KS 200 _ ltac:(lia) S200) (KS 216 _ ltac:(lia) S216)) as HS.

set (E := s21_E regsY (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr (x_fr cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 61)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R3; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R4; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (s21_E_x _ _ _ _ _ _ _ 0 _ ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (x_fr cx)) by exact (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (x_fr cx))) by exact (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 m) by exact (s21_E_x _ _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (x_cap cx)) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (x_flags cx)) by exact (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (apply BU; [exact E9 | lia]).
assert (U18 : bv_unsigned (ew E 18) = tab) by (apply BU; [exact E18 | lia]).
assert (U19 : bv_unsigned (ew E 19) = mt) by (apply BU; [exact E19 | lia]).
assert (U33 : bv_unsigned (ew E 33) = x_fr cx) by (apply BU; [exact E33 | lia]).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (x_fr cx)) by (apply BU; [exact E34 | exact Hsf]).
assert (U35 : bv_unsigned (ew E 35) = m) by (apply BU; [exact E35 | lia]).

assert (E20 : ew E 20 = w64 (mt + 16)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 20 20%bv eq_refl); exact R20).

pose proof (st_ok_pi_add_fact E _ _ 20 (PaLibF.HPTR 4) HS) as HS1.
assert (AF : afact_ok E 20 (PaLibF.HPTR 4)).
{ unfold afact_ok, PaLibF.HPTR. cbn [af_lo af_hi af_al2].
  assert (U20 : bv_unsigned (ew E 20) = mt + 16) by (apply BU; [exact E20 | lia]).
  rewrite U20. change (2 ^ 4) with 16. repeat split; lia. }
clear HS. pose proof (HS1 AF) as HS. clear HS1 AF.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) memY)) by constructor.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168) a -> rdW W memY a = rdW W memY a) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bsp.


{ cbn [ms_mem mkst].
  rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)), (U_atom E 20 (mt + 16) E20 ltac:(lia)).
  change (rd_of SEGS (mrestrict (w_H W) memY)) with (rdW W memY).
  eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinmt); rewrite ?s21_req by lia; unfold x_mtn, seg_spec.MVLAN_SIZE; lia. }
{ cbn [ss_mem add_atom]. apply awr_ok_cons_ro; [cbn; lia|]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | ]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr. s21_fold KR (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168) ltac:(fun Hr => repeat first [rewrite ew_ewset_other in Hr by lia | rewrite ew_havoc_old in Hr by lia]; rewrite ?U9 in Hr; cbv beta; lia).

lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in * end.
assert (EX : forall n, (n < 1024)%nat -> ew E' n = ew E n) by (intros nn Hnn; unfold E'; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U19' : bv_unsigned (ew E' 19) = mt) by (rewrite EX by lia; exact U19).
assert (U33' : bv_unsigned (ew E' 33) = x_fr cx) by (rewrite EX by lia; exact U33).
assert (U9' : bv_unsigned (ew E' 9) = x_s1 cx) by (rewrite EX by lia; exact U9).
pose proof (proj1 HJ) as HARs.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARs Hinmt) as (_ & _ & _ & _ & HmtpresS & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HARs Hfin) as (_ & _ & HfpresS & _).
rewrite Efr in HfpresS. rewrite HF512 in HfpresS.
pose proof (st_ok_pi_add_region E' _ _ s21_mb HS eq_refl) as HS1.
lazymatch type of HS1 with region_ok _ _ ?mm _ -> _ => assert (RT : region_ok SEGS E' mm s21_mb) end.
{ cbn [ms_mem restrict mkst]. unfold s21_mb, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19'.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HmtpresS (mt + o) ltac:(rewrite s21_req by lia; unfold x_mtn, seg_spec.MVLAN_SIZE; lia))). }
specialize (HS1 RT). clear RT.
lazymatch type of HS1 with all_disjoint _ _ ?l -> _ => assert (DT : all_disjoint E' s21_mb l) end.
{ cbn [ss_mem add_atom all_disjoint]. unfold extent_disjoint, extent_of_region, s21_mb, s21_sl1, s21_sl2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite U19', U9'. lia. }
clear HS. pose proof (HS1 DT) as HS. clear HS1 DT. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_atom] in HS.
pose proof (st_ok_pi_add_region E' _ _ s21_frn HS eq_refl) as HS1.
lazymatch type of HS1 with region_ok _ _ ?mm _ -> _ => assert (RT : region_ok SEGS E' mm s21_frn) end.
{ cbn [ms_mem restrict mkst]. unfold s21_frn, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33'.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HfpresS (x_fr cx + o) ltac:(lia))). }
specialize (HS1 RT). clear RT.
lazymatch type of HS1 with all_disjoint _ _ ?l -> _ => assert (DT : all_disjoint E' s21_frn l) end.
{ cbn [ss_mem add_atom all_disjoint]. unfold extent_disjoint, extent_of_region, s21_frn, s21_mb, s21_sl1, s21_sl2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite U19', U33', U9'.
  unfold zdisjoint in Dmtf. cbn [fst snd] in Dmtf. unfold x_mtn, seg_spec.MVLAN_SIZE in *. lia. }
clear HS. pose proof (HS1 DT) as HS. clear HS1 DT. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_atom] in HS.
pose proof (PaLibF.SRr_run_to_pi_AJ B LAWS) as RUNTOP.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168) a -> rdW W (ms_mem ms) a = rdW W memY a)
  by (intros a0 Ha0 Hn0; exact (KR a0 Ha0 Hn0)).
clear KR. rename KR2 into KR.
PaLibF.paj_run_to_sh RUNTOP HS HJ 0xcd8.


{ cbn [ss_mem].
  eapply (awr_ok_cons_gen B E' _ _ _ _ _ _ _ _ _ _ 33%nat (x_fr cx)); [reflexivity | exact U33' | |].
  { intros a Ha. cbn [s21_frn YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. rewrite Efr, HF512. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen B E' _ _ _ _ _ _ _ _ _ _ 19%nat mt); [reflexivity | exact U19' | |].
  { intros a Ha. cbn [s21_mb YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
    exists mt, (x_mtn cx). split; [exact Hinmt|]. split; [|rewrite s21_req by lia; unfold x_mtn, seg_spec.MVLAN_SIZE; lia].
    exact (s21_notin_bl0 cx ly S W mem0 md0 _ _ HAR0 Hbl ltac:(left; reflexivity)). }
  apply awr_ok_cons_ro; [cbn; lia|]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | rewrite U9'; lia | cbn; lia | cbn; lia | ]. apply awr_ok_nil. }

assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168 \/ mt + 16 <= x < mt + 20 \/ x_fr cx + 256 <= x < x_fr cx + 260) a -> rdW W (ms_mem ms) a = rdW W memY a) by (intros a0 Ha0 Hn0; apply KR; [exact Ha0 | cbv beta in *; tauto]).
clear KR. rename KR3 into KR.
s21_fold KR (fun x => x_s1 cx + 128 <= x < x_s1 cx + 168 \/ mt + 16 <= x < mt + 20 \/ x_fr cx + 256 <= x < x_fr cx + 260) ltac:(fun Hr => rewrite ?U9', ?U19', ?U33' in Hr; cbv beta; lia).


s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) A2 ltac:(apply s21_den0; rewrite EX by lia; exact E2).
s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) A3 ltac:(apply s21_den0; rewrite EX by lia; exact E3).
s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) A4 ltac:(apply s21_den0; rewrite EX by lia; exact E4).
s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) A8 ltac:(apply s21_den0; rewrite EX by lia; exact E8).
s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) A9 ltac:(apply s21_den0; rewrite EX by lia; exact E9).
s21_reg HS (16%bv : bv 5) (w64 SHADOW_OFF) A16 ltac:(apply s21_den0; rewrite EX by lia; exact E32).
s21_reg HS (18%bv : bv 5) (w64 tab) A18 ltac:(apply s21_den0; rewrite EX by lia; exact E18).
s21_reg HS (19%bv : bv 5) (w64 mt) A19 ltac:(apply s21_den0; rewrite EX by lia; exact E19).
s21_reg HS (20%bv : bv 5) (w64 (mt + 16)) A20 ltac:(apply s21_den0; rewrite EX by lia; exact E20).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s21_fsh) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
  let r3 := eval vm_compute in (nth 3 (ss_mem ssx) s21_fsh) in
  assert (HR0 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r0)
    by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity);
  assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
    by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity);
  assert (HR3 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r3)
    by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 3 r3 HS); vm_compute; reflexivity) end.
cbn [ms_mem restrict] in HR0, HR1, HR3.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 256 4%N (SLit 1) 1 HR0 U33' ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 16 4%N (SLit 33) 33 HR1 U19' ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VM.
pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region _ _ _ _ _ _ _ _ _ 128 8%N (SLit 1) 1 HR3 U9' ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as J128.
pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region _ _ _ _ _ _ _ _ _ 160 8%N (SLit 1) 1 HR3 U9' ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as J160.
clear HR0 HR1 HR3.
assert (M16 : forall j, (j < 4)%nat -> rdW W (ms_mem ms0) (mt + 16 + Z.of_nat j) = Some (le_byte 33 4 j))
  by (intros j Hj; exact (s21_aview_of_val_mem SEGS (w_H W) (ms_mem ms0) (mt + 16) 4 33 j VM Hj)).
pmkst HS.


apply (HJT cx ly S W regs0 mem0 md0 k acc c m tab mt _ _ _ Hcut); [| exact HK0 | exact HKE].
assert (Hcp : 0 < x_cap cx) by lia.
assert (T0 : x_tab0 cx = [(SegModel.S_enp, 33)]).
{ rewrite s21_tab0. destruct (Z.eqb_spec (Z.land (x_flags cx) 1) 0) as [Hq|Hq]; [contradiction|].
  destruct (Z.ltb_spec 0 (x_cap cx)) as [_|Hq2]; [reflexivity | lia]. }
assert (Etn : x_tabn cx = 18 * x_cap cx + 18) by (unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
assert (Emn : x_mtn cx = 20 * x_cap cx + 20) by (unfold x_mtn, seg_spec.MVLAN_SIZE; lia).
assert (KJ : forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rdW W (ms_mem ms0) a = rdW W mem0 a).
{ intros a Ha Hn. destruct (s21_wsP cx tab mt a ltac:(lia) Hn) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  rewrite (KR a Ha N1), (KY a Ha N2 N3 N4 N5). exact (KA a Ha N2 N6 N7 N8). }
assert (KT : forall a, tab <= a < tab + x_tabn cx -> ~ (tab <= a < tab + 7) -> ~ (tab + 16 <= a < tab + 18) ->
   ~ (tab + 18 * x_cap cx <= a < tab + 18 * x_cap cx + 18) -> rdW W (ms_mem ms0) a = rdW W mem0 a).
{ intros a Ha H1 H2 H3. destruct (s21_sepT cx tab mt a HL Ha) as (S1 & S2 & S3 & S4).
  rewrite (KR a ltac:(lia) ltac:(cbv beta; lia)), (KY a ltac:(lia) ltac:(lia) H1 H2 ltac:(lia)).
  apply KA; [lia | lia | exact H3 | lia | lia]. }
assert (KM : forall a, mt <= a < mt + x_mtn cx -> ~ (mt <= a < mt + 7) -> ~ (mt + 16 <= a < mt + 20) ->
   rdW W (ms_mem ms0) a = rdW W mem0 a).
{ intros a Ha H1 H2. destruct (s21_sepM cx tab mt a HL Ha) as (S1 & S2 & S3 & S4).
  rewrite (KR a ltac:(lia) ltac:(cbv beta; lia)), (KY a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H1).
  apply KA; [lia | lia | lia | lia | lia]. }
assert (NS1 : ~ (tab <= x_sh cx + 32 < tab + x_tabn cx)) by (intros H; destruct (s21_sepT cx tab mt _ HL H) as (_ & _ & _ & S4); lia).
assert (NS2 : ~ (mt <= x_sh cx + 32 < mt + x_mtn cx)) by (intros H; destruct (s21_sepM cx tab mt _ HL H) as (_ & _ & _ & S4); lia).
assert (NS3 : ~ (x_fr cx <= x_sh cx + 32 < x_fr cx + 512)) by (intros H; destruct (s21_sepF cx tab mt _ HL H) as (_ & S4); lia).
split; [exact HJ|]. split; [exact (conj A2 (conj (eq_trans A3 (eq_sym Hgp)) (conj (eq_trans A4 (eq_sym Htp)) (conj A8 A9))))|].
split; [exact A16|]. split; [exact A18|]. split; [exact A19|]. split; [exact A20|].
split; [exact KJ|].
rewrite T0. cbn [length Z.of_nat].
split; [exact J128|]. split; [exact J160|].
split.
{ rewrite (KR (x_sh cx + 32) ltac:(lia) ltac:(cbv beta; lia)), (KY (x_sh cx + 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact SA. }
split.
{ apply (s21_sa_val_of_val_mem SEGS (w_H W) (ms_mem ms0) (x_fr cx + FO_N) 1). exact VN. }
split.
{ apply s21_rtab_enp.
  - intros i Hi. change (length (SegModel.S_enp ++ [0])) with 7%nat in Hi.
    destruct (s21_sepT cx tab mt (tab + Z.of_nat i) HL ltac:(lia)) as (S1 & S2 & S3 & S4).
    rewrite (KR (tab + Z.of_nat i) ltac:(lia) ltac:(cbv beta; lia)). exact (ZT i ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat; lia)).
  - intros i Hi. rewrite (KT (tab + i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact (Hzt i ltac:(lia)).
  - destruct (s21_sepT cx tab mt (tab + 16) HL ltac:(lia)) as (S1 & S2 & S3 & S4).
    rewrite (KR (tab + 16) ltac:(lia) ltac:(cbv beta; lia)). exact B16.
  - destruct (s21_sepT cx tab mt (tab + 17) HL ltac:(lia)) as (S1 & S2 & S3 & S4).
    rewrite (KR (tab + 17) ltac:(lia) ltac:(cbv beta; lia)). exact B17. }
split.
{ apply s21_guard. intros i Hi.
  destruct (s21_sepT cx tab mt (tab + 18 * x_cap cx + i) HL ltac:(lia)) as (S1 & S2 & S3 & S4).
  rewrite (KR (tab + 18 * x_cap cx + i) ltac:(lia) ltac:(cbv beta; lia)).
  rewrite (KY (tab + 18 * x_cap cx + i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact (GA i Hi). }
apply s21_mtab_enp.
- intros i Hi. change (length (SegModel.S_enp ++ [0])) with 7%nat in Hi.
  destruct (s21_sepM cx tab mt (mt + Z.of_nat i) HL ltac:(lia)) as (S1 & S2 & S3 & S4).
  rewrite (KR (mt + Z.of_nat i) ltac:(lia) ltac:(cbv beta; lia)). exact (ZM i ltac:(change (length (SegModel.S_enp ++ [0])) with 7%nat; lia)).
- intros i Hi. rewrite (KM (mt + i) ltac:(lia) ltac:(lia) ltac:(lia)). exact (Hzmt i ltac:(lia)).
- pose proof (M16 0%nat ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H.
- pose proof (M16 1%nat ltac:(lia)) as H. replace (mt + 16 + Z.of_nat 1) with (mt + 17) in H by lia. exact H.
- pose proof (M16 2%nat ltac:(lia)) as H. replace (mt + 16 + Z.of_nat 2) with (mt + 18) in H by lia. exact H.
- pose proof (M16 3%nat ltac:(lia)) as H. replace (mt + 16 + Z.of_nat 3) with (mt + 19) in H by lia. exact H.
Qed.

(* ==================== the tail: m->n's check and branch (0x85a98 .. 0x85ab8) ==================== *)

Lemma s21_J : forall cx ly S W regs0 mem0 md0 k acc c m tab mt regsJ memJ mdJ,
  s21_cut cx ly S W regs0 mem0 md0 k acc c m tab mt -> s21_ptJ cx ly S W mem0 k tab mt regsJ memJ mdJ ->
  LTA_K85b0c B MT 0 -> LTA_K85e50 B MT ->
  SRr SEGS W (mkCfg (mkst regsJ (Z_to_bv 64 (BASE + 0xcd8)) memJ (seg_rom SEGS)) mdJ) (lt_post B MT cx).
Proof.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt regsJ memJ mdJ Hcut HJP HK0 HKE.
pose proof Hcut as Hcut0. s21_unpack Hcut0.
destruct HJP as (HJ & (R2 & R3 & R4 & R8 & R9) & R16 & R18 & R19 & R20 & KJ & J128 & J160 & JSH & JN & JRT & JG & JMT).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (KS : forall o v, 16 <= o <= 216 -> (o + 8 <= 88 \/ 168 <= o) -> rdword (rdW W mem0) (x_s1 cx + o) = Some v -> rdword (rdW W memJ) (x_s1 cx + o) = Some v).
{ intros o v Ho Ho2 Hv. apply (s21_rdword_keep (rdW W mem0)); [|exact Hv]. intros i Hi. apply KJ; [lia|].
  unfold s21_ws. clear -Ho Ho2 Hi Hs1 Hslo Hceil HSTK Htc Hmtc Hfrc Hsfb C1 C2 Htabn Hmtn. unfold x_sh in *. lia. }
pose proof (s21_seed2 0xcd8 18 19 18%bv 19%bv 88 128 136 160 W regsJ memJ (x_s1 cx) (x_fr cx) m (x_cap cx) (x_flags cx)
  (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) tab mt eq_refl eq_refl ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R9 R2 ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres; lia) ltac:(lia) Hfra
  ltac:(lia) Hma Hcap Hflr ltac:(lia) R18 ltac:(lia) Hta R19 ltac:(lia) Hmta
  (KS 32 _ ltac:(lia) ltac:(lia) S32) (KS 48 _ ltac:(lia) ltac:(lia) S48) (KS 56 _ ltac:(lia) ltac:(lia) S56) (KS 64 _ ltac:(lia) ltac:(lia) S64) (KS 176 _ ltac:(lia) ltac:(lia) S176)
  (KS 184 _ ltac:(lia) ltac:(lia) S184) (KS 192 _ ltac:(lia) ltac:(lia) S192) (KS 200 _ ltac:(lia) ltac:(lia) S200) (KS 216 _ ltac:(lia) ltac:(lia) S216)) as HS.

set (E := s21_E regsJ (x_fr cx) (shadow_addr (x_fr cx)) m (x_cap cx) (x_flags cx) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s21_E; apply Eimg_env).
assert (BU : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v H Hv. rewrite H, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
assert (Hsf : 0 <= shadow_addr (x_fr cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 61)); pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 3 3%bv eq_refl), R3; exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 4 4%bv eq_refl), R4; exact Htp).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 tab) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 mt) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (s21_E_x _ _ _ _ _ _ _ 0 _ ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (x_fr cx)) by exact (s21_E_x _ _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (x_fr cx))) by exact (s21_E_x _ _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 m) by exact (s21_E_x _ _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (x_cap cx)) by exact (s21_E_x _ _ _ _ _ _ _ 4 _ ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (x_flags cx)) by exact (s21_E_x _ _ _ _ _ _ _ 5 _ ltac:(lia) eq_refl).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (apply BU; [exact E9 | lia]).
assert (U18 : bv_unsigned (ew E 18) = tab) by (apply BU; [exact E18 | lia]).
assert (U19 : bv_unsigned (ew E 19) = mt) by (apply BU; [exact E19 | lia]).
assert (U33 : bv_unsigned (ew E 33) = x_fr cx) by (apply BU; [exact E33 | lia]).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (x_fr cx)) by (apply BU; [exact E34 | exact Hsf]).
assert (U35 : bv_unsigned (ew E 35) = m) by (apply BU; [exact E35 | lia]).

assert (E38 : ew E 38 = Z_to_bv 64 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) by exact (s21_E_x _ _ _ _ _ _ _ 6 _ ltac:(lia) eq_refl).
assert (HMNJ : rd32 (rdW W memJ) (m + seg_spec.MC_N) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))).
{ intros kk Hk. rewrite KJ; [exact (HMN kk Hk)| unfold seg_spec.MC_N; lia |].
  apply (s21_nws_blk cx tab mt m 9236 _ HL Dmt Dmmt Dmf Hmapp Hmc). unfold seg_spec.MC_N. lia. }
pose proof (st_ok_pi_add_region E _ _ s21_mn HS eq_refl) as HS1.
assert (RM : region_ok SEGS E (ms_mem (restrict (w_H W) (mkst regsJ (Z_to_bv 64 (BASE + 3288)) memJ (seg_rom SEGS)))) s21_mn).
{ cbn [ms_mem restrict mkst]. unfold s21_mn, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ m 0x2000 4 (SOff 38 0) (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))).
  - apply s21_den0. exact E38.
  - cbn. lia.
  - cbn. lia.
  - exact (PaLibF.val_mem_of_rd32 SEGS _ _ _ _ HMNJ). }
specialize (HS1 RM). clear RM.
assert (DM : all_disjoint E s21_mn (ss_mem (mkSS 3288 sr_atoms [s21_sl1 88 128; s21_sl2 136 160] None (s21_G 18 19)))).
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, s21_mn, s21_sl1, s21_sl2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite U35, U9. lia. }
clear HS. pose proof (HS1 DM) as HS. clear HS1 DM. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (st_ok_pi_add_fact E _ _ 38 (mkAF 0 32 0) HS) as HS1.
assert (AF : afact_ok E 38 (mkAF 0 32 0)) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (BU 38%nat _ E38 ltac:(lia)); rewrite Z.pow_0_r, Z.mod_1_r; lia).
clear HS. pose proof (HS1 AF) as HS. clear HS1 AF.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) memJ)) by constructor.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.

assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (fun x => x_s1 cx + 88 <= x < x_s1 cx + 128 \/ x_s1 cx + 136 <= x < x_s1 cx + 160) a -> rdW W memJ a = rdW W memJ a) by reflexivity.

paj_run_tok RUN HS HJ SHOK Bsp.
{ cbn [ms_mem mkst].
  rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)), (U_atom_off E 35 m 8192 E35 ltac:(lia) ltac:(lia)).
  change (rd_of SEGS (mrestrict (w_H W) memJ)) with (rdW W memJ).
  eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinm); rewrite ?(s21_req seg_spec.SEG_M_SIZE), ?HMS by (rewrite HMS; lia); lia. }
{ cbn [ss_mem add_atom]. apply awr_ok_cons_ro; [cbn; lia|]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | ]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | ]. apply awr_ok_nil. }

s21_fold KR (fun x => x_s1 cx + 88 <= x < x_s1 cx + 128 \/ x_s1 cx + 136 <= x < x_s1 cx + 160) ltac:(fun Hr => repeat first [rewrite ew_ewset_other in Hr by lia | rewrite ew_havoc_old in Hr by lia]; rewrite ?U9, ?U35 in Hr; cbv beta; lia).

pose proof (paj_run_to B LAWS) as RUNTO.
psrr_branch_tok RUN BR HS SHOK Bsp.


{ (* m->n <= 0: no segment; past the loop to K85e50 *)
  assert (Hmn0 : SegModel.mc_seg (x_mcF cx) = []).
  { lazymatch type of Hc with context [sv_denot ?Ex (SOff 38 0)] =>
      assert (D0 : sv_denot Ex (SLit 0) = Z_to_bv 64 0) by reflexivity;
      assert (D38 : sv_denot Ex (SOff 38 0) = Z_to_bv 64 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))))
        by (apply s21_den0; rewrite ew_ewset_other by lia; exact E38) end.
    rewrite D0, D38 in Hc. rewrite s21_bge0 in Hc by lia. apply Z.leb_le in Hc. destruct (SegModel.mc_seg (x_mcF cx)); [reflexivity|]. cbn [length] in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bsp 0x1090.
  { cbn [ss_mem add_atom add_cond]. apply awr_ok_cons_ro; [cbn; lia|]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite U9; lia | cbn; lia | cbn; lia | ]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite U9; lia | cbn; lia | cbn; lia | ]. apply awr_ok_nil. }
  s21_fold KR (fun x => x_s1 cx + 88 <= x < x_s1 cx + 128 \/ x_s1 cx + 136 <= x < x_s1 cx + 160) ltac:(fun Hr => repeat first [rewrite ew_ewset_other in Hr by lia | rewrite ew_havoc_old in Hr by lia]; rewrite ?U9, ?U35 in Hr; cbv beta; lia).


  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (EX : forall n, (n < 1024)%nat -> ew Ex n = ew E n) by (intros nn Hnn; rewrite ew_ewset_other by lia; reflexivity) end.
  s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) X2 ltac:(apply s21_den0; rewrite EX by lia; exact E2).
  s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) X3 ltac:(apply s21_den0; rewrite EX by lia; exact E3).
  s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) X4 ltac:(apply s21_den0; rewrite EX by lia; exact E4).
  s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) X8 ltac:(apply s21_den0; rewrite EX by lia; exact E8).
  s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) X9 ltac:(apply s21_den0; rewrite EX by lia; exact E9).
  assert (HRG : s21_rg cx (ms_regs ms0)) by exact (conj X2 (conj (eq_trans X3 (eq_sym Hgp)) (conj (eq_trans X4 (eq_sym Htp)) (conj X8 X9)))).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rdW W (ms_mem ms0) a = rdW W mem0 a).
  { intros a Ha Hn. rewrite (KR a Ha ltac:(cbv beta; unfold s21_ws in Hn; lia)). exact (KJ a Ha Hn). }
  assert (KEJ : forall a, 0 <= a < x_s1 cx -> rdW W (ms_mem ms0) a = rdW W memJ a)
    by (intros a Ha; exact (KR a ltac:(lia) ltac:(cbv beta; lia))).
  assert (SHE : rdW W (ms_mem ms0) (x_sh cx + 32) = Some 4) by (rewrite KEJ by lia; exact JSH).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
    assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity);
    assert (U9' : bv_unsigned (ew Ex 9) = x_s1 cx) by (rewrite EX by lia; exact U9) end.
  cbn [ms_mem restrict] in HR1.
  pose proof (s21_exit_core cx ly S W regs0 mem0 md0 k acc c m tab mt (ms_regs ms0) (ms_mem ms0) _ Hcut HJ HRG KE SHE)
    as (XC & XH1 & XH2 & XH3 & XH4 & XCM & XSL).

  s21_reg HS (24%bv : bv 5) (w64 m) X24 ltac:(apply s21_den0; rewrite EX by lia; exact E35).
  pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region _ _ _ _ _ _ _ _ _ 104 8%N (SOff 18 0) tab HR1 U9' ltac:(cbn [In]; tauto) ltac:(apply s21_den0; rewrite EX by lia; exact E18) ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as T104.
  pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region _ _ _ _ _ _ _ _ _ 112 8%N (SLit 0) 0 HR1 U9' ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as T112.
  pose proof (PaLibF.rdword_of_val_mem SEGS _ _ _ _ (field_of_region _ _ _ _ _ _ _ _ _ 120 8%N (SOff 19 0) mt HR1 U9' ltac:(cbn [In]; tauto) ltac:(apply s21_den0; rewrite EX by lia; exact E19) ltac:(cbn; lia) ltac:(cbn; lia)) ltac:(lia)) as T120.
  clear HR1.
  assert (T128 : rdword (rdW W (ms_mem ms0)) (x_s1 cx + 128) = Some (Z.of_nat (length (x_tab0 cx))))
    by (apply (s21_rdword_keep (rdW W memJ)); [intros i Hi; exact (KR (x_s1 cx + 128 + i) ltac:(lia) ltac:(cbv beta; lia)) | exact J128]).
  pose proof (s21_mdecl_nil (x_mcF cx) (x_tab0 cx) (x_cap cx) Hmn0) as MD.
  pmkst HS.
  apply (HKE fx cx ly S W _ _ _ k acc c m tab mt Hbase Hfrm XC XH1 XH2 XH3 XH4 X24); [| exact XCM |].
  - rewrite MD. cbn [fst snd]. rewrite Z.mod_0_l by lia.
    intros o v Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-|]); try contradiction;
      first [ exact T104 | exact T112 | exact T120 | exact T128 | apply XSL; cbn [LT_LV In]; tauto ].
  - rewrite MD. cbn [snd].
    apply (s21_tabs_keep cx (rdW W memJ) _ tab mt _ (x_s1 cx)); [intros a Ha; apply KEJ; lia | lia | lia | lia | lia | lia | lia |].
    split; [split; [pose proof (s21_tab0_len cx); lia | lia]|].
    split; [exact JRT|]. split; [exact JG|]. split; [exact JN|]. split; [exact JMT|]. exact (s21_tab0_len cx).
}

{ (* m->n > 0: turn 0 of m_declared, K85b0c *)
  assert (Hmn1 : (0 < length (SegModel.mc_seg (x_mcF cx)))%nat).
  { lazymatch type of Hc with context [sv_denot ?Ex (SOff 38 0)] =>
      assert (D0 : sv_denot Ex (SLit 0) = Z_to_bv 64 0) by reflexivity;
      assert (D38 : sv_denot Ex (SOff 38 0) = Z_to_bv 64 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))))
        by (apply s21_den0; rewrite ew_ewset_other by lia; exact E38) end.
    rewrite D0, D38, s21_bge0 in Hc by lia. apply Z.leb_gt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bsp 0xd4c.
  { cbn [ss_mem add_atom add_cond]. apply awr_ok_cons_ro; [cbn; lia|]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite U9; lia | cbn; lia | cbn; lia | ]. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 cx - x_sp0 cx)); [reflexivity | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite U9; lia | cbn; lia | cbn; lia | ]. apply awr_ok_nil. }
  s21_fold KR (fun x => x_s1 cx + 88 <= x < x_s1 cx + 128 \/ x_s1 cx + 136 <= x < x_s1 cx + 160) ltac:(fun Hr => repeat first [rewrite ew_ewset_other in Hr by lia | rewrite ew_havoc_old in Hr by lia]; rewrite ?U9, ?U35 in Hr; cbv beta; lia).


  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (EX : forall n, (n < 1024)%nat -> ew Ex n = ew E n) by (intros nn Hnn; rewrite ew_ewset_other by lia; reflexivity) end.
  s21_reg HS (2%bv : bv 5) (w64 (x_s1 cx)) X2 ltac:(apply s21_den0; rewrite EX by lia; exact E2).
  s21_reg HS (3%bv : bv 5) (w64 (as_gp B)) X3 ltac:(apply s21_den0; rewrite EX by lia; exact E3).
  s21_reg HS (4%bv : bv 5) (w64 (as_tp B)) X4 ltac:(apply s21_den0; rewrite EX by lia; exact E4).
  s21_reg HS (8%bv : bv 5) (w64 (x_sp0 cx)) X8 ltac:(apply s21_den0; rewrite EX by lia; exact E8).
  s21_reg HS (9%bv : bv 5) (w64 (x_s1 cx)) X9 ltac:(apply s21_den0; rewrite EX by lia; exact E9).
  assert (HRG : s21_rg cx (ms_regs ms0)) by exact (conj X2 (conj (eq_trans X3 (eq_sym Hgp)) (conj (eq_trans X4 (eq_sym Htp)) (conj X8 X9)))).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ s21_ws cx tab mt a -> rdW W (ms_mem ms0) a = rdW W mem0 a).
  { intros a Ha Hn. rewrite (KR a Ha ltac:(cbv beta; unfold s21_ws in Hn; lia)). exact (KJ a Ha Hn). }
  assert (KEJ : forall a, 0 <= a < x_s1 cx -> rdW W (ms_mem ms0) a = rdW W memJ a)
    by (intros a Ha; exact (KR a ltac:(lia) ltac:(cbv beta; lia))).
  assert (SHE : rdW W (ms_mem ms0) (x_sh cx + 32) = Some 4) by (rewrite KEJ by lia; exact JSH).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s21_fsh) in
    assert (HR1 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r1)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 1 r1 HS); vm_compute; reflexivity);
    assert (U9' : bv_unsigned (ew Ex 9) = x_s1 cx) by (rewrite EX by lia; exact U9) end.
  cbn [ms_mem restrict] in HR1.
  pose proof (s21_exit_core cx ly S W regs0 mem0 md0 k acc c m tab mt (ms_regs ms0) (ms_mem ms0) _ Hcut HJ HRG KE SHE)
    as (XC & XH1 & XH2 & XH3 & XH4 & XCM & XSL).

  assert (E16 : ew E 16 = w64 SHADOW_OFF) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 16 16%bv eq_refl); exact R16).
  assert (E20 : ew E 20 = w64 (mt + 16)) by (unfold E; rewrite (s21_E_reg _ _ _ _ _ _ _ 20 20%bv eq_refl); exact R20).
  s21_reg HS (16%bv : bv 5) (w64 SHADOW_OFF) X16 ltac:(apply s21_den0; rewrite EX by lia; exact E16).
  s21_reg HS (20%bv : bv 5) (w64 (Z.of_nat 0)) X20 ltac:(reflexivity).
  s21_reg HS (22%bv : bv 5) (w64 (seg_spec.mseg_addr m 0)) X22 ltac:(apply s21_den0; rewrite EX by lia; unfold seg_spec.mseg_addr; rewrite Z.mul_0_r, Z.add_0_r; exact E35).
  s21_reg HS (26%bv : bv 5) (w64 (- seg_spec.mseg_addr m 0)) X26 ltac:(unfold seg_spec.mseg_addr; rewrite Z.mul_0_r, Z.add_0_r; apply s21_neg; [rewrite EX by lia; exact E35 | lia]).
  s21_reg HS (27%bv : bv 5) (w64 (seg_spec.mseg_addr m 0)) X27 ltac:(apply s21_den0; rewrite EX by lia; unfold seg_spec.mseg_addr; rewrite Z.mul_0_r, Z.add_0_r; exact E35).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s21_fsh) in
    assert (HR2 : region_ok SEGS Ex (ms_mem (restrict Hh msx)) r2)
      by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict Hh msx) 2 r2 HS); vm_compute; reflexivity) end.
  cbn [ms_mem restrict] in HR2.

  lazymatch type of HR1 with region_ok _ ?Ex _ _ =>
  assert (D88 : sv_denot Ex (SOff 20 0) = Z_to_bv 64 (mt + 16)) by (apply s21_den0; rewrite EX by lia; exact E20);
  assert (D96 : sv_denot Ex (SAlu ALU_XOR (SOff 33 32) (SLit (-1))) = Z_to_bv 64 (lt_not (x_fr cx + FO_V)))
    by (apply s21_not; [rewrite EX by lia; exact E33 | lia | unfold FO_V; lia]);
  assert (D104 : sv_denot Ex (SOff 18 0) = Z_to_bv 64 tab) by (apply s21_den0; rewrite EX by lia; exact E18);
  assert (D112 : sv_denot Ex (SLit 0) = Z_to_bv 64 0) by reflexivity;
  assert (D120 : sv_denot Ex (SOff 19 0) = Z_to_bv 64 mt) by (apply s21_den0; rewrite EX by lia; exact E19);
  assert (D136 : sv_denot Ex (SLit 4094) = Z_to_bv 64 LT_VIDMAX) by reflexivity;
  assert (D144 : sv_denot Ex (SLit 1125899906850819) = Z_to_bv 64 LT_MASK) by reflexivity;
  assert (D152 : sv_denot Ex (SAlu ALU_XOR (SOff 19 0) (SLit (-1))) = Z_to_bv 64 (lt_not mt))
    by (replace (lt_not mt) with (lt_not (mt + 0)) by (f_equal; lia); apply s21_not; [rewrite EX by lia; exact E19 | lia | lia]);
  assert (D176 : sv_denot Ex (SAlu ALU_ADD (SAlu ALU_SRL (SOff 35 0x2000) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N)))
    by (rewrite (denot_shx _ 35 32 0x2000 m SHADOW_OFF ltac:(rewrite EX by lia; exact E35) ltac:(rewrite EX by lia; exact E32)) by (unfold SHADOW_OFF; lia); unfold shadow_addr, seg_spec.MC_N; f_equal; lia)
  end.
  s21_rdc HR1 U9' 88 D88 T88. s21_rdc HR1 U9' 96 D96 T96. s21_rdc HR1 U9' 104 D104 T104. s21_rdc HR1 U9' 112 D112 T112.
  s21_rdc HR1 U9' 120 D120 T120. s21_rdc HR2 U9' 136 D136 T136. s21_rdc HR2 U9' 144 D144 T144. s21_rdc HR2 U9' 152 D152 T152.
  assert (RS176 : 0 <= shadow_addr (m + seg_spec.MC_N) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N; pose proof (Z.div_le_upper_bound (m + 8192) 8 (2 ^ 61)); pose proof (Z.div_pos (m + 8192) 8); lia).
  s21_rdc HR2 U9' 176 D176 T176. clear RS176.
  clear HR1 HR2 D88 D96 D104 D112 D120 D136 D144 D152 D176.
  assert (T128 : rdword (rdW W (ms_mem ms0)) (x_s1 cx + 128) = Some (Z.of_nat (length (x_tab0 cx))))
    by (apply (s21_rdword_keep (rdW W memJ)); [intros i Hi; exact (KR (x_s1 cx + 128 + i) ltac:(lia) ltac:(cbv beta; lia)) | exact J128]).
  assert (T160 : rdword (rdW W (ms_mem ms0)) (x_s1 cx + 160) = Some 1)
    by (apply (s21_rdword_keep (rdW W memJ)); [intros i Hi; exact (KR (x_s1 cx + 160 + i) ltac:(lia) ltac:(cbv beta; lia)) | exact J160]).
  pose proof (s21_decl0 cx) as DC.
  pmkst HS.
  apply (HK0 fx cx ly S W _ _ _ k acc c m tab mt Hbase Hfrm Hmn1 XC XH1 XH2 XH3 XH4 X16 X20 X22 X26 X27); [| | exact XCM |].
  { rewrite DC. cbn [fst]. lia. }
  { intros o v Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (XSL o v Hin)|].
    unfold LT_LD in Hin. rewrite DC in Hin. cbn [fst snd In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-|]); try contradiction;
      first [ exact T88 | exact T96 | exact T104 | exact T112 | exact T120 | exact T128 | exact T136 | exact T144
            | exact T152 | exact T160 | exact T176 ]. }
  { rewrite DC. cbn [snd].
    apply (s21_tabs_keep cx (rdW W memJ) _ tab mt _ (x_s1 cx)); [intros a Ha; apply KEJ; lia | lia | lia | lia | lia | lia | lia |].
    split; [split; [pose proof (s21_tab0_len cx); lia | lia]|].
    split; [exact JRT|]. split; [exact JG|]. split; [exact JN|]. split; [exact JMT|]. exact (s21_tab0_len cx). }
}
Qed.

(* ====================================== the segment ====================================== *)
Lemma lt_seg_S13 : lt_seg_S13_stmt B MT.
Proof.
intros HK0 HKE.
exact (s21_stA (s21_stB (s21_P0 s21_J) (s21_P1a (s21_P1b (s21_P1c s21_J)))) HK0 HKE).
Qed.
End e.
End f.
End d.
