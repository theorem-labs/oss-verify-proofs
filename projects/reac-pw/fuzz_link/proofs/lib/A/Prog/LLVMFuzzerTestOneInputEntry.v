(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE ENTRY, from the
   function's first slot to the g_names loop head LF_gl (+0x32c), the phase `lf_entry` of
   lib/A/Prog/LLVMFuzzerTestOneInputDefs.v.

     lf_entry : forall POST, lf_from .. POST (lf_gl_inv .. 0) -> lf_start .. POST

   The walk: the frame and the saves (+0x000..+0x070); frame_alloc_4 (LinkWalkSide.v aj_gx_stack_malloc_at,
   Section hypothesis ASM4); +0x074..+0x2a4; the `beqz a3` at +0x2a8, whose other arm is refuted from
   n < 2^26 (lf_U_srl); +0x2b0..+0x304; checked_memset(g_nl, 0, NK_SIZE) at +0x304 (link_ajkit.v
   aj_gx_intrin_at, Section hypothesis CMS); +0x308..+0x328 to the cut. The cut lf_gl_inv 0 is read off the
   symbolic state (the slots, the frame's header and shadow, the cursor) and the journal (lf_jbk); g_nl is
   zero after the fill, so its byte list is NK_SIZE zero bytes.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v AD1y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Abbreviation AFL := AF_LLVMFuzzerTestOneInput.

Definition lf_regions0 : smem :=
  [stack_region LF_MFRAME; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 65); uar_cell_regionP (A_OBJ 65)].
Definition lf_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
    [] [].
Definition lf_ss0 : sstate := mkSS LF_entry sr_atoms lf_regions0 None lf_facts0.
Definition lf_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the runs after frame_alloc_4 make no instrumented check, and the frame's shadow is a region of their state *)
Definition lf_span0 : Z * Z := (0, 0).

(* The shift-right of a 64-bit value by a literal (pcap's PcapHarnessPE.v pe_U_srl, origin/ossv/recipes). *)
Lemma lf_U_srl : forall E x k, 0 <= k < 64 -> U E (SAlu ALU_SRL x (SLit k)) = U E x / 2 ^ k.
Proof.
intros E x k Hk. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E x) as Hr. unfold M64 in *.
assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
assert (Hle : U E x / 2 ^ k <= U E x).
{ apply Z.div_le_upper_bound; [exact Hp|].
  assert (H1 : 1 <= 2 ^ k) by (rewrite <- (Z.pow_0_r 2); apply Z.pow_le_mono_r; lia).
  rewrite Z.mul_comm. rewrite <- (Z.mul_1_r (U E x)) at 1. apply Z.mul_le_mono_nonneg_l; lia. }
assert (Hge : 0 <= U E x / 2 ^ k) by (apply Z.div_pos; lia).
revert Hle Hge. generalize (U E x / 2 ^ k). intros q Hle Hge.
apply zcanon_id. unfold M64. lia.
Qed.

(* ==========================================================================
   The image data the set-up invariant names (lf_odd_at, lf_texts_at, lf_la_at, lf_gnames_w): the two pointer
   tables of .data.rel.ro with their .rodata strings, which are read-only image bytes and which `arodata_okP`
   pins at every state of the call, and the two .bss objects the body writes (msg_build.long_alias and
   g_names), whose bytes the image shows and whose segment is writable. Every number below is read from the
   pin (sha256 059dae63e07c) and checked against the image module by the vm_compute lemmas.
   ========================================================================== *)

Definition lf_romb (a : Z) : option byte := seg_rom tfibsegs (Z_to_bv 64 a).

(* the image's bytes at [lo, lo + |bs|) are bs *)
Definition lf_rom_is (lo : Z) (bs : list byte) : bool :=
  forallb (fun i => match lf_romb (lo + Z.of_nat i) with
                    | Some b => Z.eqb (bv_unsigned b) (bv_unsigned (nth i bs (Z_to_bv 8 0)))
                    | None => false end)
          (seq 0 (length bs)).

(* the image shows every byte of [lo, lo + n) *)
Definition lf_rom_some (lo n : Z) : bool :=
  forallb (fun i => match lf_romb (lo + Z.of_nat i) with Some _ => true | None => false end)
          (seq 0 (Z.to_nat n)).

(* the eight bytes of a little-endian word *)
Definition lf_wb (v : Z) : list byte := map (fun k => Z_to_bv 8 (v / 2 ^ (8 * Z.of_nat k) mod 256)) (seq 0 8).

(* [lo, lo + n) is read-only: inside one non-writable segment, or inside the relro window *)
Definition lf_ro_seg (lo n : Z) : bool :=
  existsb (fun s => (negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (lo + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool) tfibsegs.
Definition lf_relro (lo n : Z) : bool := ((PCAP_RLO <=? lo) && (lo + n <=? PCAP_RHI))%bool.
Definition lf_ro_any (lo n : Z) : bool := (lf_ro_seg lo n || lf_relro lo n)%bool.
(* and outside the memory-checking runtime's statics and outside errno *)
Definition lf_ns (lo n : Z) : bool :=
  (forallb (fun r => ((lo + n <=? fst r) || (fst r + snd r <=? lo))%bool) Tfib_owned_static
   && ((lo + n <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? lo)))%bool.

Definition lf_str_chk (q : Z) (s : list byte) : bool :=
  (negb (q =? 0) && (0 <=? q) && (q + Z.of_nat (length s) + 1 <=? 2 ^ 64) &&
   lf_ro_any q (Z.of_nat (length s) + 1) && lf_ns q (Z.of_nat (length s) + 1) &&
   lf_rom_is q (s ++ [Z_to_bv 8 0]) && negb (existsb (fun b => bv_unsigned b =? 0) s))%bool.
Definition lf_ptr_chk (tab : Z) (i : nat) (q : Z) : bool :=
  (lf_ro_any (tab + 8 * Z.of_nat i) 8 && lf_ns (tab + 8 * Z.of_nat i) 8 &&
   lf_rom_is (tab + 8 * Z.of_nat i) (lf_wb q) && (rdn (lf_wb q) 0 8 =? q))%bool.

Definition LF_ODD_PTRS : list Z := [0x20fc0; 0x20fe0; 0x21000; 0x21020; 0x21040; 0x21060].
Definition LF_TXT_PTRS : list Z :=
  [0x20fc0; 0x21100; 0x21120; 0x21140; 0x21160; 0x21180; 0x211a0; 0x211c0; 0x211e0; 0x21200; 0x21220].
Definition LF_TXT_STRS : list (list byte) :=
  map (fun l => map (fun z => Z_to_bv 8 z) l)
    [[];
     [114;101;97;99;45;112;119;58;115;101;114;118;101;100];
     [114;101;97;99;45;112;119;58;109;105;110;116;101;100];
     [104;111;115;116;45;97;108;105;97;115];
     [114;101;97;99;45;112;119;58];
     [114;101;97;99;45;112;119;58;115;101;114;118;101;100;50];
     [114;101;97;99;45;112;119];
     [118;108;97;110];
     [118;101;116;104];
     [118;108;97;110;120];
     [118;108;97]].

Definition lf_odd_b : bool :=
  forallb (fun i => (lf_ptr_chk LA_ODD i (nth i LF_ODD_PTRS 0) &&
                     lf_str_chk (nth i LF_ODD_PTRS 0) (nth i lf_odd_strs []))%bool) (seq 0 6).
Definition lf_txt_b : bool :=
  forallb (fun i => (lf_ptr_chk LA_TEXTS i (nth i LF_TXT_PTRS 0) &&
                     lf_str_chk (nth i LF_TXT_PTRS 0) (nth i LF_TXT_STRS []))%bool) (seq 0 11).

Lemma lf_odd_ok : lf_odd_b = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_txt_ok : lf_txt_b = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_la_rom1 : lf_rom_some LA_LONG_ALIAS 300 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_la_rom2 : lf_rom_some (LA_LONG_ALIAS + 301) 3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_gn_rom : lf_rom_some LA_G_NAMES G_NAMES_SIZE = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_la_wseg : wseg_ok tfibsegs (Z_to_bv 64 LA_LONG_ALIAS) (Z.to_nat 304) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lf_la_writable : forall (m : word -> option byte) a,
  LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304 -> writable_at tfibsegs m a.
Proof.
intros m. apply writable_at_of_wseg; [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia | exact lf_la_wseg].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation VAL := (pa_val).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

Hypothesis LV : LinkVals.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis PS : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis ASM4 : astack_malloc_realizes pa_segs B 4.
(* checked_memset (0x53214): lib/A/AE2r.v:568 `asan_memset_realizes` at this B, in its exact shape (W5); at the
   instance (pa_segs = tfibsegs by definition, LinkImgInst.v) it is `asan_memset_realizes B LAWS PS`. *)
Hypothesis CMS : forall ly S (W : world pa_segs) regs mem md d x n,
  ecall_pre pa_segs B ly S W regs mem md ->
  getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d ->
  d + n <= 2 ^ 63 ->
  dest_ok pa_segs B ly S W regs mem d n ->
  range_addressable (aview pa_segs (w_H W) mem) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview pa_segs (w_H W) mem) d n) ->
  amem_range d n ->
  SRr pa_segs W (cfg_at pa_segs 0x53214 regs mem md)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at pa_segs (raZ regs) regs' mem' md' /\
    AR pa_segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 d /\
    (forall i, 0 <= i < n -> aview pa_segs (w_H W) mem' (d + i) = Some (x mod 256)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
       aview pa_segs (w_H W) mem' a = aview pa_segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* the same closed form, in the premise order of YG0d.v's aintrin_realizes, which link_ajkit.v's lift takes *)
Lemma lf_memset_intrin : aintrin_realizes pa_segs B OSet 0x53214.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
exact (CMS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.

Lemma lf_obj_vals :
  pa_val (A_OBJ 0) = 0xa1a28 /\ pa_val (A_OBJ 1) = 0xa19d0 /\ pa_val (A_OBJ 2) = 0x5dcac0 /\
  pa_val (A_OBJ 3) = 0x1672f /\ pa_val (A_OBJ 4) = 0x827d4 /\ pa_val (A_OBJ 5) = 0x62fac0 /\
  pa_val (A_OBJ 6) = 0x20fa0 /\ pa_val (A_OBJ 64) = 0xaa438 /\ pa_val (A_OBJ 65) = 0xaa440 /\
  pa_val A_TEXT = 0x821cc.
Proof.
  repeat split; first [rewrite (lv_text LV); reflexivity | rewrite (lv_obj LV) by (vm_compute; lia); reflexivity].
Qed.

(* ---- the image facts of the set-up invariant, from the checks above ---- *)

Lemma lf_wb_len : forall v, length (lf_wb v) = 8%nat.
Proof. intros v. unfold lf_wb. rewrite length_map, length_seq. reflexivity. Qed.

Lemma lf_nonul : forall s : list byte,
  negb (existsb (fun b : byte => bv_unsigned b =? 0) s) = true -> ~ In (Z_to_bv 8 0) s.
Proof.
intros s H Hin. apply negb_true_iff in H.
assert (Hx : existsb (fun b : byte => bv_unsigned b =? 0) s = true).
{ apply existsb_exists. exists (Z_to_bv 8 0). split; [exact Hin | vm_compute; reflexivity]. }
rewrite Hx in H. discriminate H.
Qed.

(* every byte of a checked range: read-only image, not a static of the memory-checking runtime, not errno *)
Lemma lf_ro_sound : forall lo n, lf_ro_any lo n = true -> lf_ns lo n = true ->
  forall a, lo <= a < lo + n ->
  in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros lo n Hro Hns a Ha. split; [|split].
- rewrite HSEGS. unfold in_roP. unfold lf_ro_any in Hro. apply orb_prop in Hro as [Hro|Hro].
  + left. unfold lf_ro_seg in Hro. apply existsb_exists in Hro as (s & Hin & Hb).
    apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
    apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    exists s. split; [exact Hin|]. split; [exact H1 | lia].
  + right. unfold lf_relro in Hro. apply andb_prop in Hro as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- rewrite (ts_owned B PS). unfold lf_ns in Hns. apply andb_prop in Hns as [H1 _].
  rewrite forallb_forall in H1. intros HE. apply Exists_exists in HE as (r & Hr & Hz).
  unfold in_zr in Hz. pose proof (H1 r Hr) as X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
- rewrite (ts_errno B PS). unfold lf_ns in Hns. apply andb_prop in Hns as [_ H2].
  apply orb_prop in H2 as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* the bytes of a read-only range, which arodata_okP pins to the image's own *)
Lemma lf_abytes_ro : forall (m : word -> option byte) lo bs,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (ard SEGS m) ->
  0 <= lo -> lo + Z.of_nat (length bs) <= 2 ^ 64 ->
  lf_ro_any lo (Z.of_nat (length bs)) = true -> lf_ns lo (Z.of_nat (length bs)) = true ->
  lf_rom_is lo bs = true ->
  abytes SEGS m lo bs.
Proof.
intros m lo bs HR Hlo Hhi Hro Hns His.
split; [exact Hlo|]. split; [exact Hhi|].
intros i Hi.
unfold lf_rom_is in His. rewrite forallb_forall in His.
pose proof (His i ltac:(apply in_seq; lia)) as X.
destruct (lf_romb (lo + Z.of_nat i)) as [b|] eqn:Hrom; [|discriminate X].
apply Z.eqb_eq in X.
destruct (lf_ro_sound lo (Z.of_nat (length bs)) Hro Hns (lo + Z.of_nat i) ltac:(lia)) as (H1 & H2 & H3).
pose proof (HR (lo + Z.of_nat i) H1 H2 H3) as HA.
assert (Hr2 : seg_rom SEGS (Z_to_bv 64 (lo + Z.of_nat i)) = Some b)
  by (rewrite HSEGS; exact Hrom).
unfold ard in HA. rewrite Hr2 in HA.
destruct (mbyte SEGS m (lo + Z.of_nat i)) as [b'|] eqn:Hm; cbn [option_map] in HA; [|discriminate HA].
injection HA as HA.
assert (Hne : nth_error bs i = Some (nth i bs (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
rewrite Hne.
f_equal. apply bv_eq. rewrite HA, X. reflexivity.
Qed.

(* a word of the image, from its eight bytes *)
Lemma lf_val_w8 : forall (m : word -> option byte) a q,
  abytes SEGS m a (lf_wb q) -> rdn (lf_wb q) 0 8 = q -> au64_at SEGS m a q.
Proof.
intros m a q HB Hr.
pose proof (val_mem_of_abytes SEGS m a (lf_wb q) 0 8%nat HB ltac:(lia)
  ltac:(rewrite lf_wb_len; lia)) as H.
change (Z.of_nat 8) with 8 in H. rewrite Hr, Z.add_0_r in H. exact H.
Qed.

(* every byte of a range the image shows is a byte of memory *)
Lemma lf_mbyte_some : forall (m : word -> option byte) lo n, lf_rom_some lo n = true ->
  forall i, (i < Z.to_nat n)%nat -> exists b, mbyte SEGS m (lo + Z.of_nat i) = Some b.
Proof.
intros m lo n H i Hi. unfold lf_rom_some in H. rewrite forallb_forall in H.
pose proof (H i ltac:(apply in_seq; lia)) as X.
destruct (lf_romb (lo + Z.of_nat i)) as [b|] eqn:Hrom; [|discriminate X].
unfold mbyte. destruct (m (Z_to_bv 64 (lo + Z.of_nat i))) as [b'|] eqn:Hm; [exists b'; reflexivity|].
exists b. rewrite HSEGS. unfold lf_romb in Hrom. exact Hrom.
Qed.

Lemma lf_abytes_img : forall (m : word -> option byte) lo n,
  lf_rom_some lo n = true -> 0 <= lo -> 0 <= n -> lo + n <= 2 ^ 64 ->
  abytes SEGS m lo (abytes_of SEGS m lo (Z.to_nat n)).
Proof.
intros m lo n H Hlo Hn Hhi.
apply (abytes_of_abytes SEGS m lo (Z.to_nat n) Hlo ltac:(lia)).
intros i Hi. exact (lf_mbyte_some m lo n H i Hi).
Qed.

(* the odd table of .data.rel.ro and its six strings *)
Lemma lf_odd_at_holds : forall (m : word -> option byte),
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (ard SEGS m) -> lf_odd_at m.
Proof.
intros m HR i Hi.
pose proof lf_odd_ok as HB. unfold lf_odd_b in HB. rewrite forallb_forall in HB.
pose proof (HB i ltac:(apply in_seq; lia)) as X. clear HB.
apply andb_prop in X as [XP XS].
unfold lf_ptr_chk in XP.
apply andb_prop in XP as [XP Xrdn]. apply andb_prop in XP as [XP Xis]. apply andb_prop in XP as [Xro Xns].
apply Z.eqb_eq in Xrdn.
unfold lf_str_chk in XS.
apply andb_prop in XS as [XS Xnn]. apply andb_prop in XS as [XS Xsis]. apply andb_prop in XS as [XS Xsns].
apply andb_prop in XS as [XS Xsro]. apply andb_prop in XS as [XS Xq64]. apply andb_prop in XS as [Xq0 Xqlo].
apply negb_true_iff in Xq0. apply Z.eqb_neq in Xq0.
apply Z.leb_le in Xqlo. apply Z.leb_le in Xq64.
exists (nth i LF_ODD_PTRS 0).
split; [|split; [exact Xq0 | split]].
- apply (lf_val_w8 m (LA_ODD + 8 * Z.of_nat i) (nth i LF_ODD_PTRS 0)); [|exact Xrdn].
  apply (lf_abytes_ro m (LA_ODD + 8 * Z.of_nat i) (lf_wb (nth i LF_ODD_PTRS 0)) HR).
  + unfold LA_ODD. lia.
  + rewrite lf_wb_len. unfold LA_ODD. lia.
  + rewrite lf_wb_len. exact Xro.
  + rewrite lf_wb_len. exact Xns.
  + exact Xis.
- split; [|apply lf_nonul; exact Xnn].
  apply (lf_abytes_ro m (nth i LF_ODD_PTRS 0) (nth i lf_odd_strs [] ++ [Z_to_bv 8 0]) HR).
  + exact Xqlo.
  + rewrite length_app. cbn [length]. lia.
  + rewrite length_app. cbn [length].
    replace (Z.of_nat (length (nth i lf_odd_strs []) + 1))
      with (Z.of_nat (length (nth i lf_odd_strs [])) + 1) by lia.
    exact Xsro.
  + rewrite length_app. cbn [length].
    replace (Z.of_nat (length (nth i lf_odd_strs []) + 1))
      with (Z.of_nat (length (nth i lf_odd_strs [])) + 1) by lia.
    exact Xsns.
  + exact Xsis.
- intros j Hj.
  exact (proj1 (lf_ro_sound (nth i LF_ODD_PTRS 0) (Z.of_nat (length (nth i lf_odd_strs [])) + 1)
                 Xsro Xsns (nth i LF_ODD_PTRS 0 + j) ltac:(lia))).
Qed.

(* the texts table of .data.rel.ro and its eleven strings *)
Lemma lf_texts_at_holds : forall (m : word -> option byte),
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (ard SEGS m) -> lf_texts_at m.
Proof.
intros m HR i Hi.
pose proof lf_txt_ok as HB. unfold lf_txt_b in HB. rewrite forallb_forall in HB.
pose proof (HB i ltac:(apply in_seq; lia)) as X. clear HB.
apply andb_prop in X as [XP XS].
unfold lf_ptr_chk in XP.
apply andb_prop in XP as [XP Xrdn]. apply andb_prop in XP as [XP Xis]. apply andb_prop in XP as [Xro Xns].
apply Z.eqb_eq in Xrdn.
unfold lf_str_chk in XS.
apply andb_prop in XS as [XS Xnn]. apply andb_prop in XS as [XS Xsis]. apply andb_prop in XS as [XS Xsns].
apply andb_prop in XS as [XS Xsro]. apply andb_prop in XS as [XS Xq64]. apply andb_prop in XS as [Xq0 Xqlo].
apply negb_true_iff in Xq0. apply Z.eqb_neq in Xq0.
apply Z.leb_le in Xqlo. apply Z.leb_le in Xq64.
exists (nth i LF_TXT_PTRS 0), (nth i LF_TXT_STRS []).
split; [|split; [exact Xq0 | split]].
- apply (lf_val_w8 m (LA_TEXTS + 8 * Z.of_nat i) (nth i LF_TXT_PTRS 0)); [|exact Xrdn].
  apply (lf_abytes_ro m (LA_TEXTS + 8 * Z.of_nat i) (lf_wb (nth i LF_TXT_PTRS 0)) HR).
  + unfold LA_TEXTS. lia.
  + rewrite lf_wb_len. unfold LA_TEXTS. lia.
  + rewrite lf_wb_len. exact Xro.
  + rewrite lf_wb_len. exact Xns.
  + exact Xis.
- split; [|apply lf_nonul; exact Xnn].
  apply (lf_abytes_ro m (nth i LF_TXT_PTRS 0) (nth i LF_TXT_STRS [] ++ [Z_to_bv 8 0]) HR).
  + exact Xqlo.
  + rewrite length_app. cbn [length]. lia.
  + rewrite length_app. cbn [length].
    replace (Z.of_nat (length (nth i LF_TXT_STRS []) + 1))
      with (Z.of_nat (length (nth i LF_TXT_STRS [])) + 1) by lia.
    exact Xsro.
  + rewrite length_app. cbn [length].
    replace (Z.of_nat (length (nth i LF_TXT_STRS []) + 1))
      with (Z.of_nat (length (nth i LF_TXT_STRS [])) + 1) by lia.
    exact Xsns.
  + exact Xsis.
- intros j Hj.
  exact (proj1 (lf_ro_sound (nth i LF_TXT_PTRS 0) (Z.of_nat (length (nth i LF_TXT_STRS [])) + 1)
                 Xsro Xsns (nth i LF_TXT_PTRS 0 + j) ltac:(lia))).
Qed.

(* g_names: 512 writable bytes of .bss, which the image shows *)
Lemma lf_gnames_w_holds : forall (m : word -> option byte), lf_gnames_w m.
Proof.
intros m. unfold lf_gnames_w, abuf.
exists (abytes_of SEGS m LA_G_NAMES (Z.to_nat G_NAMES_SIZE)). split.
- rewrite abytes_of_length. unfold G_NAMES_SIZE. lia.
- split.
  + apply (lf_abytes_img m LA_G_NAMES G_NAMES_SIZE lf_gn_rom);
      unfold LA_G_NAMES, G_NAMES_SIZE; lia.
  + intros k Hk. rewrite abytes_of_length in Hk. rewrite HSEGS. apply LA_G_NAMES_writable.
    unfold G_NAMES_SIZE in Hk. lia.
Qed.

(* msg_build.long_alias: its 300 bytes, the NUL the Pre carries, and strlen's three slack bytes *)
Lemma lf_la_at_holds : forall (m : word -> option byte),
  val_mem SEGS m (LA_LONG_ALIAS + 300) 1 0 -> lf_la_at m.
Proof.
intros m HN. split; [|split; [exact HN|]].
- exists (abytes_of SEGS m LA_LONG_ALIAS (Z.to_nat 300)). split.
  + split.
    * apply (lf_abytes_img m LA_LONG_ALIAS 300 lf_la_rom1); unfold LA_LONG_ALIAS; lia.
    * intros k Hk. rewrite abytes_of_length in Hk. rewrite HSEGS. apply lf_la_writable. lia.
  + rewrite abytes_of_length. lia.
- exists (abytes_of SEGS m (LA_LONG_ALIAS + 301) (Z.to_nat 3)). split.
  + split.
    * apply (lf_abytes_img m (LA_LONG_ALIAS + 301) 3 lf_la_rom2); unfold LA_LONG_ALIAS; lia.
    * intros k Hk. rewrite abytes_of_length in Hk. rewrite HSEGS. apply lf_la_writable. lia.
  + rewrite abytes_of_length. reflexivity.
Qed.

(* ---- reading a region of the symbolic state back (pcap's PcapHarnessPE.v pe_cbyte .. pe_saved_of, which are
   GrantEntryHead.v's; copied and renamed) ---- *)
Definition lf_cbyte (cs : list YP09.chunk) (i : Z) : option Z :=
  match find (fun c => Z.eqb (YP09.c_off c) i) cs with
  | Some c => match YP09.c_val c with
              | CVal w v => if N.eqb w 1 then match v with SLit z => Some (zcanon z mod 256) | _ => None end
                            else None
              | _ => None end
  | None => None
  end.
Definition lf_chunks_match (cs : list YP09.chunk) (sh : list Z) : bool :=
  forallb (fun i => match lf_cbyte cs (Z.of_nat i) with Some v => Z.eqb v (nth i sh 0) | None => false end)
          (seq 0 (length sh)).
Definition lf_cword (cs : list YP09.chunk) (i : Z) : option sv :=
  match find (fun c => Z.eqb (YP09.c_off c) i) cs with
  | Some c => match YP09.c_val c with CVal w v => if N.eqb w 8 then Some v else None | _ => None end
  | None => None
  end.

Lemma lf_shadow_bytes : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs sh,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  lf_chunks_match cs sh = true ->
  forall i, (i < length sh)%nat -> aview SEGS H m (base + Z.of_nat i) = Some (nth i sh 0).
Proof.
intros E H m nn base lo hi wlo whi cs sh Hr Hb Hm i Hi.
unfold lf_chunks_match in Hm. rewrite forallb_forall in Hm.
specialize (Hm i ltac:(apply in_seq; lia)).
destruct (lf_cbyte cs (Z.of_nat i)) as [v|] eqn:Hc; [|discriminate Hm].
apply Z.eqb_eq in Hm.
unfold lf_cbyte in Hc.
destruct (find (fun c => Z.eqb (YP09.c_off c) (Z.of_nat i)) cs) as [c|] eqn:Hf; [|discriminate Hc].
destruct (find_some _ _ Hf) as [Hin Hoff]. apply Z.eqb_eq in Hoff.
destruct (YP09.c_val c) as [w z| | |] eqn:Hv; try discriminate Hc.
destruct (N.eqb w 1) eqn:Hw; [|discriminate Hc]. apply N.eqb_eq in Hw. subst w.
destruct z as [zz| | | | | | | | | |]; try discriminate Hc.
injection Hc as <-.
destruct Hr as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs c Hin) as Hck.
cbn [YP09.r_base YP09.base_val] in Hck. rewrite Hb in Hck.
specialize (Hck 0 ltac:(unfold YP09.c_len; rewrite Hv; cbn [YP09.cv_len]; lia)).
destruct Hck as (b & Hcb & Hmb).
rewrite Hv in Hcb. cbn [YP09.cbyte] in Hcb. injection Hcb as <-.
rewrite Hoff, Z.add_0_r in Hmb.
unfold aview. rewrite Hmb. cbn [option_map]. f_equal. rewrite <- Hm.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. reflexivity.
Qed.

Lemma lf_word_of_region : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v.
Proof.
intros E H m nn base lo hi wlo whi cs off e v Hr Hb Hin He Hv.
apply (rdword_of_val_mem SEGS H m); [|exact Hv].
change 8%nat with (N.to_nat 8).
exact (field_of_region E (mrestrict H m) nn base cs lo hi wlo whi off 8%N e v Hr Hb Hin He
  ltac:(cbn [Z.of_N]; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Lemma lf_word_at : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  lf_cword cs off = Some e ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v.
Proof.
intros E H m nn base lo hi wlo whi cs off e v Hr Hb Hc He Hv.
unfold lf_cword in Hc.
destruct (find (fun c => Z.eqb (YP09.c_off c) off) cs) as [c|] eqn:Hf; [|discriminate Hc].
destruct (find_some _ _ Hf) as [Hin Hoff]. apply Z.eqb_eq in Hoff.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hoff, Hc, Hin.
destruct cv as [w z| | |]; try discriminate Hc.
destruct (N.eqb w 8) eqn:Hw; [|discriminate Hc]. apply N.eqb_eq in Hw.
injection Hc as Hc. subst w. subst co. subst z.
exact (lf_word_of_region E H m nn base lo hi wlo whi cs off _ v Hr Hb Hin He Hv).
Qed.

(* the thirteen saved words of the machine frame *)
Lemma lf_saved_of : forall E (H : word -> bool) (m : word -> option byte) sp0 (regs : bvmap 5 word)
  lo hi wlo whi cs,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2%nat) = sp0 ->
  (forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r) ->
  lf_cword cs (-8) = Some (SOff 1%nat 0) ->
  lf_cword cs (-16) = Some (SOff 8%nat 0) ->
  lf_cword cs (-24) = Some (SOff 9%nat 0) ->
  lf_cword cs (-32) = Some (SOff 18%nat 0) ->
  lf_cword cs (-40) = Some (SOff 19%nat 0) ->
  lf_cword cs (-48) = Some (SOff 20%nat 0) ->
  lf_cword cs (-56) = Some (SOff 21%nat 0) ->
  lf_cword cs (-64) = Some (SOff 22%nat 0) ->
  lf_cword cs (-72) = Some (SOff 23%nat 0) ->
  lf_cword cs (-80) = Some (SOff 24%nat 0) ->
  lf_cword cs (-88) = Some (SOff 25%nat 0) ->
  lf_cword cs (-96) = Some (SOff 26%nat 0) ->
  lf_cword cs (-104) = Some (SOff 27%nat 0) ->
  rdword (aview SEGS H m) (sp0 - 8) = Some (bv_unsigned (getr regs 1%bv)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS H m) (sp0 - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
Proof.
intros E H m sp0 regs lo hi wlo whi cs Hr Hb HEE K1 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
assert (W1 : forall (nn : nat) (r : bv 5) off e,
  Z.of_nat nn = bv_unsigned r -> e = SOff nn 0 -> lf_cword cs off = Some e ->
  rdword (aview SEGS H m) (sp0 + off) = Some (bv_unsigned (getr regs r))).
{ intros nn r off e Hn He Hc. subst e.
  apply (lf_word_at E H m 2%nat sp0 lo hi wlo whi cs off (SOff nn 0) _ Hr Hb Hc);
    [| pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hb64;
       change (bv_modulus 64) with (2 ^ 64) in Hb64; lia].
  cbn [sv_denot]. rewrite (HEE nn r Hn), Z.add_0_r. reflexivity. }
split.
- replace (sp0 - 8) with (sp0 + -8) by lia. exact (W1 1%nat 1%bv (-8) _ eq_refl eq_refl K1).
- intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9
               \/ j = 10 \/ j = 11) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]]]]];
  [ replace (sp0 - 16 - 8 * 0) with (sp0 + -16) by lia
  | replace (sp0 - 16 - 8 * 1) with (sp0 + -24) by lia
  | replace (sp0 - 16 - 8 * 2) with (sp0 + -32) by lia
  | replace (sp0 - 16 - 8 * 3) with (sp0 + -40) by lia
  | replace (sp0 - 16 - 8 * 4) with (sp0 + -48) by lia
  | replace (sp0 - 16 - 8 * 5) with (sp0 + -56) by lia
  | replace (sp0 - 16 - 8 * 6) with (sp0 + -64) by lia
  | replace (sp0 - 16 - 8 * 7) with (sp0 + -72) by lia
  | replace (sp0 - 16 - 8 * 8) with (sp0 + -80) by lia
  | replace (sp0 - 16 - 8 * 9) with (sp0 + -88) by lia
  | replace (sp0 - 16 - 8 * 10) with (sp0 + -96) by lia
  | replace (sp0 - 16 - 8 * 11) with (sp0 + -104) by lia ];
  cbn [Z.ltb Z.compare Z.add];
  [ exact (W1 8%nat (8%bv : bv 5) (-16) _ eq_refl eq_refl K8)
  | exact (W1 9%nat (9%bv : bv 5) (-24) _ eq_refl eq_refl K9)
  | exact (W1 18%nat (18%bv : bv 5) (-32) _ eq_refl eq_refl K18)
  | exact (W1 19%nat (19%bv : bv 5) (-40) _ eq_refl eq_refl K19)
  | exact (W1 20%nat (20%bv : bv 5) (-48) _ eq_refl eq_refl K20)
  | exact (W1 21%nat (21%bv : bv 5) (-56) _ eq_refl eq_refl K21)
  | exact (W1 22%nat (22%bv : bv 5) (-64) _ eq_refl eq_refl K22)
  | exact (W1 23%nat (23%bv : bv 5) (-72) _ eq_refl eq_refl K23)
  | exact (W1 24%nat (24%bv : bv 5) (-80) _ eq_refl eq_refl K24)
  | exact (W1 25%nat (25%bv : bv 5) (-88) _ eq_refl eq_refl K25)
  | exact (W1 26%nat (26%bv : bv 5) (-96) _ eq_refl eq_refl K26)
  | exact (W1 27%nat (27%bv : bv 5) (-104) _ eq_refl eq_refl K27) ].
Qed.

(* ---- small algebra the cut needs ---- *)
Lemma lf_nth_repeat : forall (x : byte) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof.
intros x n. induction n as [|n IH]; intros i Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [repeat nth_error]. apply IH. lia.
Qed.

Lemma lf_rdn4_zero : forall (bs : list byte) off,
  (forall i, (i < length bs)%nat -> nth_error bs i = Some (Z_to_bv 8 0)) ->
  0 <= off -> off + 4 <= Z.of_nat (length bs) -> rdn bs off 4 = 0.
Proof.
intros bs off Hz Hoff Hlen.
change (rdn bs off 4 = 0) with (rdn bs off (Z.of_nat 4%nat) = 0).
apply (rdn_of_vals bs off 4%nat 0); [exact Hoff | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia |].
intros k Hk. rewrite (Hz (Z.to_nat off + k)%nat ltac:(lia)). f_equal. f_equal.
unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma lf_mbyte0 : forall (H : word -> bool) (mm : word -> option byte) a,
  aview SEGS H mm a = Some 0 -> mbyte SEGS (mrestrict H mm) a = Some (Z_to_bv 8 0).
Proof.
intros H mm a Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mm) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Hv. vm_compute. reflexivity.
Qed.

Lemma lf_sbm_fds : forall m m', same_but_materialized m m' ->
  m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof.
intros m m' Hs.
pose proof (wvb_fds_fs (m_vm_lazy m) (m_vm_materialized m') m) as [E1 E2].
rewrite <- E1, <- E2. rewrite <- (same_but_materialized_wvb m m' Hs). split; reflexivity.
Qed.

Lemma lf_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
intros a Ha. rewrite HSEGS. destruct pcap_relro_in_image as (s & Hs & H1 & H2 & H3).
exists s. split; [exact Hs | lia].
Qed.

Lemma lf_roP_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (lf_relro_img a Hr)].
Qed.

(* no read-only byte of the image lies in g_nl *)
Definition lf_gnl_rofree : bool :=
  (forallb (fun s => (seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? LA_G_NL)
                      || (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base s)))%bool) tfibsegs
   && ((PCAP_RHI <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? PCAP_RLO)))%bool.
Lemma lf_gnl_rofree_ok : lf_gnl_rofree = true. Proof. vm_compute. reflexivity. Qed.

Lemma lf_roP_not_gnl : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE).
Proof.
intros a Hro Hg. pose proof lf_gnl_rofree_ok as HB. unfold lf_gnl_rofree in HB.
apply andb_prop in HB as [H1 H2].
destruct Hro as [(s & Hs & Hw & Hr) | Hr].
- rewrite HSEGS in Hs. rewrite forallb_forall in H1. pose proof (H1 s Hs) as X.
  rewrite Hw in X. cbn [orb] in X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
- apply orb_prop in H2 as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* the bytes the memory FILE's invariant reads outside its block: the three heads and the three stdio words *)
Definition LF_AMF_RNG : list (Z * Z) :=
  [(amf_sink_addr link_amf, 8); (amf_say_addr link_amf, 8); (amf_ofl_head link_amf, 8);
   (amf_threaded link_amf, 1); (amf_need_locks link_amf, 1); (amf_ofl_lock link_amf, 4)].
Definition lf_amf_chk : bool :=
  forallb (fun r => (lf_ns (fst r) (snd r) && (0x10000 <=? fst r) && (fst r + snd r <=? IMG_TOP)
                     && ((fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r)))%bool) LF_AMF_RNG.
Lemma lf_amf_ok : lf_amf_chk = true. Proof. vm_compute. reflexivity. Qed.

Lemma lf_amf_addr : forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a ->
  exists r, In r LF_AMF_RNG /\ fst r <= a < fst r + snd r.
Proof.
intros a Ha.
cbv [amf_head_addr amf_env_addr amf_ofl_head amf_sink_addr amf_say_addr amf_threaded amf_need_locks
     amf_ofl_lock link_amf] in Ha.
unfold LF_AMF_RNG. cbv [amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock amf_threaded amf_need_locks
     link_amf].
destruct Ha as [[H|[H|H]] | [H|[H|H]]].
- eexists. split; [left; reflexivity | cbn [fst snd]; lia].
- eexists. split; [right; left; reflexivity | cbn [fst snd]; lia].
- eexists. split; [right; right; left; reflexivity | cbn [fst snd]; lia].
- eexists. split; [right; right; right; left; reflexivity | cbn [fst snd]; lia].
- eexists. split; [right; right; right; right; left; reflexivity | cbn [fst snd]; lia].
- eexists. split; [right; right; right; right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma lf_ro_sound_ns : forall lo n, lf_ns lo n = true -> forall a, lo <= a < lo + n ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros lo n Hns a Ha. unfold lf_ns in Hns. apply andb_prop in Hns as [H1 H2]. split.
- rewrite (ts_owned B PS). rewrite forallb_forall in H1. intros HE. apply Exists_exists in HE as (r & Hr & Hz).
  unfold in_zr in Hz. pose proof (H1 r Hr) as X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
- rewrite (ts_errno B PS). apply orb_prop in H2 as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma lf_amf_facts : forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE).
Proof.
intros a Ha. destruct (lf_amf_addr a Ha) as (r & Hr & Hin).
pose proof lf_amf_ok as HB. unfold lf_amf_chk in HB. rewrite forallb_forall in HB.
pose proof (HB r Hr) as X.
apply andb_prop in X as [X Xg]. apply andb_prop in X as [X Xhi]. apply andb_prop in X as [Xns Xlo].
apply Z.leb_le in Xlo. apply Z.leb_le in Xhi.
destruct (lf_ro_sound_ns (fst r) (snd r) Xns a Hin) as (H2 & H3).
split; [|split; [exact H2 | split; [exact H3|]]].
- rewrite HSEGS. apply in_img_hull. unfold pcap_img_end. lia.
- apply orb_prop in Xg as [X|X]; apply Z.leb_le in X; lia.
Qed.

Definition lf_nul_chk : bool :=
  (lf_ns LA_NUL 1 && (0x10000 <=? LA_NUL) && (LA_NUL + 1 <=? IMG_TOP)
   && ((LA_NUL + 1 <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? LA_NUL)))%bool.
Lemma lf_nul_ok : lf_nul_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_nul_facts : in_img SEGS LA_NUL /\ ~ Exists (in_zr LA_NUL) (as_owned_static B) /\
  ~ (as_errno B <= LA_NUL < as_errno B + 4) /\ ~ (LA_G_NL <= LA_NUL < LA_G_NL + NK_SIZE).
Proof.
pose proof lf_nul_ok as HB. unfold lf_nul_chk in HB.
apply andb_prop in HB as [HB Hg]. apply andb_prop in HB as [HB Hhi]. apply andb_prop in HB as [Hns Hlo].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
destruct (lf_ro_sound_ns LA_NUL 1 Hns LA_NUL ltac:(lia)) as (H2 & H3).
split; [|split; [exact H2 | split; [exact H3|]]].
- rewrite HSEGS. apply in_img_hull. unfold pcap_img_end. lia.
- apply orb_prop in Hg as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* a word of a region of the symbolic state, its chunk found by evaluation *)
Ltac lf_rd HR U off :=
  lazymatch type of HR with
  | YP09.region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      let r := eval vm_compute in (lf_cword cs off) in
      lazymatch r with
      | Some ?ex => apply (lf_word_at Ex _ _ _ _ _ _ _ _ cs off ex _ HR U ltac:(vm_compute; reflexivity))
      end
  end.

#[local] Abbreviation FROM POST GI :=
  (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation START POST :=
  (lf_start SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST).
#[local] Abbreviation GL j := (lf_gl_inv B MT MS la_nul j).

(* the symbolic state at the first slot *)
Lemma lf_entry0 : forall (regs : bvmap 5 word) ly S (W : world SEGS) mem md n,
  afn_pre SEGS B LLVMF_STK ly S W regs mem md [] ->
  getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SHADOW_OFF])) lf_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LF_entry)) mem (seg_rom SEGS))).
Proof.
intros regs ly S W mem md n HPRE H11 Hn26.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & Hpres & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
destruct lf_obj_vals as (V0 & V1 & _ & _ & _ & _ & _ & V64 & V65 & _).
set (E := Eimg (Ereg regs [w64 SHADOW_OFF])).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs [w64 SHADOW_OFF]) nn)
  by (intros nn Hnn; subst E; apply Eimg_low; exact Hnn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
{ intros nn v Hnn Hv. cbn [base_val]. rewrite Hnn. apply unsigned_lit_small. exact Hv. }
pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 1%nat ltac:(lia)) as EO1.
pose proof (EO 64%nat ltac:(lia)) as EO64. pose proof (EO 65%nat ltac:(lia)) as EO65.
rewrite V0 in EO0, Kguar. rewrite V1 in EO1, Kgot. rewrite V64 in EO64, Kgot, Kcell.
rewrite V65 in EO65, Kguar, Kuar.
rewrite restrict_mkst_fx. unfold lf_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lf_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [unfold LF_MFRAME; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable pa_segs). apply Hpres. unfold LF_MFRAME, LLVMF_STK in *. lia.
  + fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
      [cbn [sv_denot]; rewrite EO64, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) mem _ _ Kgot).
  + fold E. rewrite (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ 0xaa438 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) mem _ _ Kcell).
  + fold E. rewrite (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ 0xa1a28 0 8 (SOff (A_OBJ 65) 0) 0xaa440);
      [cbn [sv_denot]; rewrite EO65, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) mem _ _ Kguar).
  + fold E. rewrite (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ 0xaa440 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 pa_segs (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold lf_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)), (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)),
    (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)), (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, LF_MFRAME. cbn [fst snd].
  unfold LLVMF_STK in *.
  revert Hslo Hshi H47 Hceil C1a Hstk0. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [lf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  unfold LLVMF_STK in *.
  revert Hslo Hshi H47 Hceil C1a Hstk0 Hsp0al Hn26.
  clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* The write obligation of every run after frame_alloc_4: the regions are, in order, the frame's shadow (atom 62),
   the frame (atom 44), s1's slots (atom 60, at sp1 = sp0 + d) and the saves (atom 2, sp0). *)
Ltac lf_awr fp F SH d U60 U44 U62 U3_2 Hfb ESH :=
  apply awr_ok_x_of0;
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end;
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 62%nat SH); [reflexivity | exact U62 | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists LF_CID, fp;
    split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd]; unfold LF_CID; fold F; rewrite ESH, Hfb;
    change (1024 / 8) with 128; lia |];
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 44%nat F); [reflexivity | exact U44 | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists LF_CID, fp;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; unfold LF_CID; fold F; rewrite Hfb; lia |];
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat d);
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |];
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite U3_2; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |];
  apply awr_ok_nil.

Lemma lf_entry : forall POST, FROM POST (GL 0) -> START POST.
Proof.
intros POST HNEXT cx HB.
pose proof HB as HB0.
destruct HB as (HPRE & Hfrm & HGX & Hlanul & HMS & HE0 & HE02 & HCTX & Hmo1 & Hmo2 & Hmo3 & Hmo4 & Hmo5 & HML &
  MFSL).
destruct HPRE as (HFN & Hra & H10 & H11 & Hpn & Hnl & HPL & Hfr0 & Hev0 & Hlive0 & HROD & HGI & HTincl & HnT &
  HENV & HHL & HNUL & HFDN & HFSS & HMOK & HWR).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HFN as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hn26 : 0 <= c_n cx < 2 ^ 26) by (unfold c_n in *; destruct Hpn as [[-> _] | [Hn _]]; lia).
pose proof (lf_entry0 (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_n cx) HFN H11 Hn26) as HS.
pose proof (ajournal_gx_init (SK := SK) SEGS B G_HARNESS 0 [] LLVMF_STK (amf_harness_fp (c_T cx)) _ _ _ _ _ _ _ HFN
  ltac:(lia) ltac:(reflexivity) ltac:(unfold LLVMF_STK in *; lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg (c_regs cx) [w64 SHADOW_OFF])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (c_regs cx) r)
  by (intros q r Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ (c_regs cx)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (rdW (c_W cx) (c_mem cx))) by constructor.
clear HEdef.
unfold lf_sp1 in *. unfold cfg_at.
change (w64 (BASE + LF_entry)) with (Z_to_bv 64 (BASE + LF_entry)).
pose (RUNX := paj_run_x SK B LAWS G_HARNESS HGX 0 []).
(* +0x000 .. +0x070: the frame, the saves, s0, the realignment, the two cells, a0 := 0x380, jal frame_alloc_4 *)
paj_run_tok RUNX HS HJ SHOK lf_span.
{ apply awr_ok_x_of0.
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (c_regs cx) - 416 <= a < spZ (c_regs cx)) ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ apply (kept_of_frame (segs := SEGS) E (ss_mem lf_ss0) (w_H (c_W cx)) (c_mem cx) (ms_mem ms) _ HFr).
  intros bb wlo whi a Hin Ha. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?Usp in Ha; clear - Ha; lia |]).
  destruct Hin. }
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P1.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (2%bv : bv 5) R2.
assert (Esp0 : ew E 2 = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
set (sp1 := lf_sp1_of (spZ (c_regs cx))).
destruct (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) Hsp0al)
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16. unfold LF_MFRAME in Hsp1r.
assert (Hsp1v : sp1 = 32 * ((spZ (c_regs cx) + -416) / 32))
  by (unfold sp1, lf_sp1_of, LF_MFRAME; f_equal; f_equal; lia).
assert (Rsp1 : getr (ms_regs ms) 2 = Z_to_bv 64 sp1).
{ rewrite R2.
  change (alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (ew E 2) + -416)) (Z_to_bv 64 (-32)))
    with (sv_denot E (SAlu ALU_AND (SOff 2 (-416)) (SLit (-32)))).
  rewrite (denot_and_m32 E 2 (spZ (c_regs cx)) (-416) Esp0) by (unfold LLVMF_STK in *; lia).
  rewrite Hsp1v. reflexivity. }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick (trim_stack rs (-104) 0) [0]%nat) in
  pose proof (st_ok_submem SEGS Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; submem_to) ltac:(vm_compute; reflexivity))
    as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
assert (Hspms : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Rsp1, unsigned_lit_small by lia; reflexivity).
(* ---- frame_alloc_4(0x380) at +0x070 (0x3ddc4), on the gx journal (LinkWalkSide.v aj_gx_stack_malloc_at) ---- *)
assert (Hpc4 : pc_stack_malloc (as_code B) 4 = 0x3ddc4) by (rewrite (ts_code B PS); vm_compute; reflexivity).
rewrite (lv_sigma LV). change (link_sigma LS___asan_stack_malloc_4) with 0x3ddc4.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ apply (aj_gx_stack_malloc_at SK SEGS B LAWS Hsegs (pal_env B TL) 4 ASM4 ltac:(lia) 0x3ddc4 G_HARNESS 0 []
    (c_W cx) (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [] (c_ly cx) (c_S cx) _ 0 (getr (ms_regs ms) 1) Hpc4 HJ).
  - rewrite Hspms. exact Hsp1al16.
  - rewrite Hspms, Hes. unfold LLVMF_STK. lia.
  - rewrite Hspms. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. clear R2 R3 R4.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fp & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 &
  HES2 & HF4096 & HFceil & Hz & Hflag & HK & Hsame2 & HRAW).
rewrite R1. clear R1.
rewrite Hspms, Hes in HK, HRAW.
rewrite Hfr0 in Hfrs2, Hnin.
pose proof (fun a Ha => aj_gx_present SK SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 a Ha) as Hpres2.
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _). clear memS2 HJi2.
jafter_call_keep_pi HS 40%nat regs2 (rdW (c_W cx) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). pose proof HK as (K1 & _). apply K1; [unfold LLVMF_STK in *; lia | lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. unfold LLVMF_STK. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
clear HE1.
(* the class-4 frame F (a0 after the call: atom 44), its flag FL and its shadow SH *)
assert (Hfin2 : In (LF_CID, fp) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
set (F := frame_addr (c_ly cx) 4 fp) in *.
set (FL := flag_addr (c_ly cx) 4 fp) in *.
assert (Hfb : fs_frame_bytes 4 = 1024) by (vm_compute; reflexivity).
rewrite Hfb in Hflag, Hz, HFceil.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10, Ha0; reflexivity). clear R10.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fp HAR2 Hfin2) as (HF32 & HFapp & HFpres & HSHpres).
change (frame_addr (c_ly cx) 4 fp) with F in HF32, HFapp, HFpres, HSHpres.
rewrite Hfb in HFapp, HFpres, HSHpres. change (1024 / 8) with 128 in HSHpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ 4 fp HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLlt).
change (flag_addr (c_ly cx) 4 fp) with FL in HFLpres, HFLown, HFLapp, HFLlt.
assert (HF64 : F mod 64 = 0).
{ unfold F. eapply proj1. eapply frame_al64; first [exact LAWS | exact HAR2 | exact Hfin2]. }
set (SH := shadow_of_addr SHADOW_OFF F).
assert (ESH : shadow_addr F = SH) by reflexivity.
rewrite ESH in HSHpres.
assert (HSHr : SHADOW_OFF + 512 <= SH /\ SH + 128 <= SHADOW_OFF + 2 ^ 44 /\ SH mod 8 = 0).
{ unfold SH, shadow_of_addr. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  destruct (div8_of_mul64 F HF64) as [E8 E64]. rewrite E8.
  unfold SHADOW_OFF. split; [lia|]. split; [lia|].
  replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z_mod_mult. }
assert (DFSH : F + 1024 <= SH \/ SH + 128 <= F)
  by (unfold SH, shadow_of_addr; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia).
(* sp and s1: rebound to the atom 60 = sp1 (the engine places no store through a masked address) *)
assert (E12 : ew Ev1 2 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact Esp0).
prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ (c_regs cx)) (-416) E12) in Rsp2 by (unfold LLVMF_STK in *; lia).
rewrite (denot_and_m32_add0 Ev1 2 (spZ (c_regs cx)) (-416) E12) in Rs12 by (unfold LLVMF_STK in *; lia).
rewrite <- Hsp1v in Rsp2, Rs12.
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1; Z_to_bv 64 FL; Z_to_bv 64 SH] HS
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1; Z_to_bv 64 FL; Z_to_bv 64 SH]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 60)%nat -> ew E3v nn = ew Ev1 nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E3v 60 = Z_to_bv 64 sp1)
  by (rewrite HE3; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1; Z_to_bv 64 FL; Z_to_bv 64 SH] 0 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E61 : ew E3v 61 = Z_to_bv 64 FL)
  by (rewrite HE3; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1; Z_to_bv 64 FL; Z_to_bv 64 SH] 1 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 SH)
  by (rewrite HE3; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1; Z_to_bv 64 FL; Z_to_bv 64 SH] 2 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (HEI3 : img_env VAL A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI1 | cbv; lia]).
clear HE3.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rsp2))
    as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rs12))
    as HS3 end.
clear HS; rename HS3 into HS.
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD3 by lia; exact E12).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD3, OLD1 by lia; exact E32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3 by lia; exact E44).
assert (E3_62 : ew E3v 62 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (rewrite E62; reflexivity).
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = SH) by (rewrite E62; apply unsigned_lit_small; unfold SHADOW_OFF in HSHr; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ (c_regs cx)) by (rewrite E3_2; apply unsigned_lit_small; lia).
add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32;
        unfold LLVMF_STK in *; repeat split; lia).
add_fact HS 44%nat (HPTR 6)
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E3_44, unsigned_lit_small by lia;
        change (2 ^ 6) with 64; repeat split; lia).
add_fact HS 62%nat (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 3)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E62, unsigned_lit_small by (unfold SHADOW_OFF in HSHr; lia);
        change (2 ^ 3) with 8; unfold SHADOW_OFF in *; repeat split; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS
    (shadow_decl_ok Ev 44 32 62 F SHADOW_OFF E3_44 ltac:(lia) E3_32 E3_62)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* the three regions the rest of the prologue writes: s1's slots, the frame (its flag pointer at 1016) and the
   frame's 112 shadow bytes *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 0x138 0 0x138 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem
          restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply Hpres2; unfold LLVMF_STK in *; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in
          change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite U60, U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 4 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks
          base_val ms_mem restrict mkst app];
        rewrite Hfb, U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS _ _ F 1016 8 _ FL);
          [cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; unfold in_app in HFLapp; lia | cbn; lia
          | replace (F + 1016) with (F + 1024 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in
          change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite Hfb, U60, U44, U3_2; unfold LLVMF_STK in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 4 0 112 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks
          base_val ms_mem restrict mkst app];
        rewrite Hfb, U62; change (1024 / 8) with 128; split; [unfold SHADOW_OFF in HSHr; lia|];
        split; [unfold SHADOW_OFF in HSHr; lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HSHpres o ltac:(lia))) | apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in
          change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite Hfb, U60, U44, U62, U3_2; change (1024 / 8) with 128; unfold LLVMF_STK in *;
        unfold SHADOW_OFF in HSHr; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E3v (rdW (c_W cx) mem2)) by constructor.
clear SHOK.
pose (Zw := fun a => (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/ (sp1 <= a < sp1 + 0x138) \/
  (F <= a < F + 1024) \/ (SH <= a < SH + 128)).
(* ---- +0x074 .. +0x2a4: s4 := F, `bnez s4` decided by F >= 4096 (the real-stack arm +0x088 .. +0x0a0 is not
   entered), slot 0x110 := F, the header, the 112 shadow bytes, a3 := n >> 26 ---- *)
paj_run_tok RUNX HS HJ2 SHOK2 lf_span0.
{ lf_awr fp F SH (sp1 - spZ (c_regs cx)) U60 U44 U62 U3_2 Hfb ESH. }
lazymatch type of HS with context [restrict _ ?m] =>
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zw a ->
  aview SEGS (w_H (c_W cx)) (ms_mem m) a = aview SEGS (w_H (c_W cx)) mem2 a) end.
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ _ HFr) end.
  intros bb wlo whi a Hin Ha. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha;
    rewrite ?U60, ?U44, ?U62, ?U3_2 in Ha; unfold Zw; clear - Ha; lia |]).
  destruct Hin. }
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
clear HF HFr HG.
assert (E3_11 : ew E3v 11 = Z_to_bv 64 (c_n cx))
  by (rewrite OLD3, OLD1 by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11).
pose (BR := paj_branch (PI := PI)).
(* +0x2a8 `beqz a3` on a3 = n >> 26: taken, since the Pre bounds n below 2 ^ 26; the early return +0x2ac is not
   reached *)
psrr_branch_tok RUNX BR HS SHOK2 lf_span0.
2: { exfalso. rewrite branch_eq_U in Hc. rewrite (lf_U_srl _ _ 26 ltac:(lia)) in Hc.
     rewrite (U_atom _ 11%nat (c_n cx) E3_11) in Hc by lia. rewrite (U_lit _ 0) in Hc by lia.
     rewrite (Z.div_small (c_n cx) (2 ^ 26)) in Hc by lia. cbn in Hc. discriminate Hc. }
clear Hc.
(* ---- +0x2b0 .. +0x304: the eleven slots, the cursor, s2 := g_nl, a0 .. a2, jal checked_memset ---- *)
paj_run_tok RUNX HS HJ2 SHOK2 lf_span0.
{ lf_awr fp F SH (sp1 - spZ (c_regs cx)) U60 U44 U62 U3_2 Hfb ESH. }
lazymatch type of HS with context [restrict _ ?m] =>
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ Zw a ->
  aview SEGS (w_H (c_W cx)) (ms_mem m) a = aview SEGS (w_H (c_W cx)) mem2 a) end.
{ intros a Ha Hzw. rewrite <- (KR2 a Ha Hzw).
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ Zw HFr) end; [|exact Ha | exact Hzw].
  intros bb wlo whi a' Hin Ha'. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha';
    rewrite ?U60, ?U44, ?U62, ?U3_2 in Ha'; unfold Zw; clear - Ha'; lia |]).
  destruct Hin. }
pose proof (fun x Hp => apresent_grows _ _ _ x HG (P2 x Hp)) as P3.
clear HF HFr HG KR2 P2.
lazymatch type of HS with context [restrict _ ?m] => rename m into msR3 end.
(* ---- checked_memset(g_nl, 0, 271992) at +0x304 (0x53214), lifted by link_ajkit.v aj_gx_intrin_at: g_nl is in
   G_HARNESS and in a writable segment, its shadow is zero at every AR state (LinkWalkZsh.v zsh_gnl) ---- *)
pmkst HS.
rewrite (lv_sigma LV). change (link_sigma LS___asan_memset) with 0x53214.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
destruct lf_obj_vals as (V0 & V1 & V2 & V3 & V4 & V5 & V6 & V64 & V65 & VT).
assert (EG2 : ew E3v (A_OBJ 2) = Z_to_bv 64 LA_G_NL)
  by (rewrite (img_env_atomP E3v (A_OBJ 2) HEI3) by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (Hspm3 : spZ (ms_regs msR3) = sp1) by (unfold spZ; rewrite Q2, E60, unsigned_lit_small by lia; reflexivity).
pose proof HJ2 as (_ & _ & (memSx & HJix & _) & _). pose proof HJix as (HAR3 & _). clear memSx HJix.
assert (ZG : range_addressable (aview SEGS (w_H (c_W cx)) (ms_mem msR3)) SHADOW_OFF LA_G_NL NK_SIZE /\
  shadow_hull_vis (aview SEGS (w_H (c_W cx)) (ms_mem msR3)) LA_G_NL NK_SIZE)
  by (eapply zsh_gnl; first [exact PS | exact HAR3]).
eapply SRr_bind.
{ apply (aj_gx_intrin_at SK SEGS B LAWS Hsegs OSet 0x53214 lf_memset_intrin G_HARNESS 0 [] (c_W cx) (ms_regs msR3)
    (ms_mem msR3) LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(LF_CID, fp)] (c_ly cx) S2 _ 0 LA_G_NL 0 271992 (getr (ms_regs msR3) 1) HGX HJ2).
  - rewrite Q10. exact EG2.
  - exact Q11.
  - exact Q12.
  - lia.
  - unfold LA_G_NL. lia.
  - unfold LA_G_NL. lia.
  - rewrite Hspm3. exact Hsp1al16.
  - rewrite Hspm3, Hes. unfold LLVMF_STK in *. lia.
  - rewrite Hspm3. lia.
  - rewrite Q3, OLD3, OLD1, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Q4, OLD3, OLD1, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. right; left. split.
    + apply (inG_of_In G_HARNESS LA_G_NL 271992 a); [left; reflexivity | exact Ha].
    + generalize (rdW (c_W cx) (ms_mem msR3)). intros m. rewrite HSEGS. apply LA_G_NL_writable. exact Ha.
  - left. unfold kLowMemEnd, LA_G_NL. lia.
  - exact (proj1 ZG).
  - intros _. exact (proj2 ZG).
  - exact I. }
cbv beta. clear Q2 Q3 Q4 Q10 Q11 Q12.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H10m & Hset & Heff & Hpres3 & Hsame3).
rewrite Q1. clear Q1.
rewrite Hspm3, Hes in Heff.
assert (HAC : alloc_ceiling + 16384 <= sp1 - 4096) by (unfold LLVMF_STK in *; lia).
assert (HFimg : forall a, F <= a < F + 1024 -> ~ in_img SEGS a).
{ intros a Ha. apply (frm_img _ _ LAWS _ _ _ _ _ 4 fp a HAR2 Hfin2). rewrite Hfb. exact Ha. }
assert (HGimg : forall a, LA_G_NL <= a < LA_G_NL + 271992 -> in_img SEGS a).
{ intros a Ha. rewrite HSEGS. apply in_img_hull. unfold LA_G_NL in Ha.
  unfold pcap_img_end, YImgTop.IMG_TOP. lia. }
jafter_call_keep_pi HS 64%nat regs3 (rdW (c_W cx) mem3) HP3 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview (segs := SEGS) E3v (w_H (c_W cx)) (ms_mem msR3) mem3 62%nat SH 0 128 0 112 _ U62);
      [intros a Ha; apply Heff; unfold SHADOW_OFF, LA_G_NL in *; lia | exact Hpres3].
  - apply (region_kept_aview (segs := SEGS) E3v (w_H (c_W cx)) (ms_mem msR3) mem3 44%nat F 0 1024 0 1024 _ U44);
      [|exact Hpres3].
    intros a Ha. apply Heff; [lia | intros Hg; apply (HFimg a ltac:(lia)); exact (HGimg a Hg) | lia].
  - apply (region_kept_aview (segs := SEGS) E3v (w_H (c_W cx)) (ms_mem msR3) mem3 60%nat sp1 0 0x138 0 0x138 _ U60);
      [intros a Ha; apply Heff; unfold LA_G_NL in *; lia | exact Hpres3].
  - apply (region_kept_aview (segs := SEGS) E3v (w_H (c_W cx)) (ms_mem msR3) mem3 2%nat (spZ (c_regs cx))
      (-104) 0 (-104) 0 _ U3_2);
      [intros a Ha; apply Heff; unfold LA_G_NL in *; lia | exact Hpres3]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E3v 64 (map (getr regs3) CLOB)) as E4v eqn:HE4 in HS.
assert (HEIms : img_env VAL A_LIM E4v) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall nn, (nn < 64)%nat -> ew E4v nn = ew E3v nn)
  by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
clear HE4.
assert (U4_60 : bv_unsigned (ew E4v 60) = sp1) by (rewrite OLD4 by lia; exact U60).
assert (U4_44 : bv_unsigned (ew E4v 44) = F) by (rewrite OLD4 by lia; exact U44).
assert (U4_62 : bv_unsigned (ew E4v 62) = SH) by (rewrite OLD4 by lia; exact U62).
assert (U4_2 : bv_unsigned (ew E4v 2) = spZ (c_regs cx)) by (rewrite OLD4 by lia; exact U3_2).
assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] E4v (rdW (c_W cx) mem3)) by constructor.
clear SHOK2.
pose (RUNTOX := paj_run_to_x SK B LAWS G_HARNESS HGX 0 []).
(* ---- +0x308 .. +0x328: the eight constants, falling into the loop head LF_gl ---- *)
paj_run_to_tok RUNTOX HS HJ3 SHOK3 lf_span0 LF_gl.
{ lf_awr fp F SH (sp1 - spZ (c_regs cx)) U4_60 U4_44 U4_62 U4_2 Hfb ESH. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msG end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ Zw a ->
  aview SEGS (w_H (c_W cx)) (ms_mem msG) a = aview SEGS (w_H (c_W cx)) mem3 a).
{ intros a Ha Hzw.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ Zw HFr) end; [|exact Ha | exact Hzw].
  intros bb wlo whi a' Ha' Hin. vm_compute in Ha'.
  repeat (destruct Ha' as [Hq | Ha']; [injection Hq as <- <- <-; cbn [base_val] in Hin;
    rewrite ?U4_60, ?U4_44, ?U4_62, ?U4_2 in Hin; unfold Zw; clear - Hin; lia |]).
  destruct Ha'. }
clear HF HFr HG.
(* what the whole segment left alone: the image outside g_nl, and the caller's blocks *)
assert (HimgZ : forall a, in_img SEGS a -> ~ Zw a /\ ~ (sp1 - 4096 <= a < sp1)).
{ intros a Hi. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow. split.
  - intros [Hq|[Hq|[Hq|Hq]]].
    + unfold LLVMF_STK in *; lia.
    + unfold LLVMF_STK in *; lia.
    + exact (HFimg a Hq Hi).
    + unfold SHADOW_OFF in HSHr; lia.
  - unfold LLVMF_STK in *; lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE) ->
  aview SEGS (w_H (c_W cx)) (ms_mem msG) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ intros a Hi Hns Her Hgn. destruct (HimgZ a Hi) as [HZ Hsp].
  pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  pose proof HK as (_ & _ & K3 & _).
  rewrite (KR4 a ltac:(lia) HZ), (Heff a ltac:(lia) ltac:(intros HH; apply Hgn; unfold NK_SIZE; lia) Hsp),
    (KR3 a ltac:(lia) HZ), (K3 a Hi Hns Her).
  apply KR1; [lia | unfold LLVMF_STK in *; lia]. }
assert (KBLK : forall b nb i, In (b, nb) (ablocks B (c_ly cx) (c_S cx)) -> 0 <= i < req_size nb ->
  aview SEGS (w_H (c_W cx)) (ms_mem msG) (b + i) = aview SEGS (w_H (c_W cx)) (c_mem cx) (b + i)).
{ intros b nb i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b nb HAR Hin) as (Hmod & Hb4096 & Hbceil & Hbapp & _).
  assert (Hni : ~ in_img SEGS (b + i))
    by (apply (blk_img _ _ LAWS _ _ _ _ _ b nb (b + i) HAR Hin); lia).
  pose proof (sep_block_frame _ _ LAWS _ _ _ _ _ b nb 4 fp HAR2 ltac:(rewrite Eab; exact Hin) Hfin2) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Hfb in Hdj. fold F in Hdj.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF in HSHr.
  assert (HnZ : ~ Zw (b + i))
    by (intros [Hq|[Hq|[Hq|Hq]]]; unfold LLVMF_STK, alloc_ceiling in *; lia).
  assert (Hw : 0 <= b + i < 2 ^ 64) by (unfold alloc_ceiling in *; lia).
  pose proof HK as (_ & K2 & _).
  rewrite (KR4 _ Hw HnZ),
    (Heff _ Hw ltac:(intros HH; apply Hni; apply HGimg; unfold NK_SIZE in *; lia)
       ltac:(unfold alloc_ceiling in *; lia)),
    (KR3 _ Hw HnZ).
  rewrite (K2 b nb i Hin Hi (fun Hq : False => Hq)).
  apply KR1; [unfold alloc_ceiling in *; lia | unfold LLVMF_STK, alloc_ceiling in *; lia]. }
assert (KIN : forall a, 0 <= a < c_n cx ->
  aview SEGS (w_H (c_W cx)) (ms_mem msG) (c_p cx + a) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + a)).
{ intros a Ha. destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
  apply (KBLK (c_p cx) (c_n cx) a Hin). unfold req_size.
  destruct (Z.eqb_spec (c_n cx) 0) as [Hq|Hq]; lia. }
(* the registers and the four regions at the cut *)
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
spregion HS 0%nat HRsh. spregion HS 1%nat HRf. spregion HS 2%nat HRs1. spregion HS 3%nat HRst.
assert (E4_32 : ew E4v 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD4 by lia; exact E3_32).
assert (E4_44 : ew E4v 44 = Z_to_bv 64 F) by (rewrite OLD4 by lia; exact E3_44).
assert (E4_61 : ew E4v 61 = Z_to_bv 64 FL) by (rewrite OLD4 by lia; exact E61).
assert (E4_60 : ew E4v 60 = Z_to_bv 64 sp1) by (rewrite OLD4 by lia; exact E60).
assert (E4_10 : ew E4v 10 = Z_to_bv 64 (c_p cx))
  by (rewrite OLD4, OLD3, OLD1 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E4_11 : ew E4v 11 = Z_to_bv 64 (c_n cx))
  by (rewrite OLD4, OLD3, OLD1 by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (EEcut : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 40)%nat ->
  ew E4v nn = getr (c_regs cx) r)
  by (intros nn r Hn Hlt; rewrite OLD4, OLD3, OLD1 by lia; exact (EE nn r Hn)).
assert (EO2 : ew E4v (A_OBJ 2) = Z_to_bv 64 LA_G_NL).
{ rewrite (img_env_atomP E4v (A_OBJ 2) HEIms) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V2. reflexivity. }
change (A_OBJ 2) with 243%nat in EO2.
assert (EO3 : ew E4v (A_OBJ 3) = Z_to_bv 64 LA_DESCR).
{ rewrite (img_env_atomP E4v (A_OBJ 3) HEIms) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V3. reflexivity. }
change (A_OBJ 3) with 244%nat in EO3.
assert (EO4 : ew E4v (A_OBJ 4) = Z_to_bv 64 (link_text + AFL)).
{ rewrite (img_env_atomP E4v (A_OBJ 4) HEIms) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V4. reflexivity. }
change (A_OBJ 4) with 245%nat in EO4.
assert (EO5 : ew E4v (A_OBJ 5) = Z_to_bv 64 LA_G_NAMES).
{ rewrite (img_env_atomP E4v (A_OBJ 5) HEIms) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V5. reflexivity. }
change (A_OBJ 5) with 246%nat in EO5.
assert (EO6 : ew E4v (A_OBJ 6) = Z_to_bv 64 LA_STR).
{ rewrite (img_env_atomP E4v (A_OBJ 6) HEIms) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V6. reflexivity. }
change (A_OBJ 6) with 247%nat in EO6.
assert (UO2 : bv_unsigned (ew E4v 243%nat) = LA_G_NL)
  by (rewrite EO2; apply unsigned_lit_small; unfold LA_G_NL; lia).
(* the arodata and the g_nl bytes at the cut *)
assert (HRODc : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H (c_W cx)) (ms_mem msG))).
{ intros a Hro Hns Her.
  rewrite (KIMG a (lf_roP_img a Hro) Hns Her (lf_roP_not_gnl a Hro)). exact (HROD a Hro Hns Her). }
assert (HGZ : forall i, 0 <= i < NK_SIZE ->
  mbyte SEGS (rdW (c_W cx) (ms_mem msG)) (LA_G_NL + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. apply lf_mbyte0.
  rewrite (KR4 (LA_G_NL + i) ltac:(unfold LA_G_NL, NK_SIZE in *; lia)
    ltac:(apply (proj1 (HimgZ _ (HGimg (LA_G_NL + i) ltac:(unfold NK_SIZE in Hi; lia))))) ).
  rewrite (Hset i ltac:(unfold NK_SIZE in Hi; lia)). reflexivity. }
assert (HNULc : val_mem SEGS (rdW (c_W cx) (ms_mem msG)) la_nul 1 0).
{ intros k Hk. destruct lf_nul_facts as (Hi & Hns & Her & Hgn).
  rewrite Hlanul in *. replace (LA_NUL + Z.of_nat k) with LA_NUL by lia.
  rewrite (mbyte_of_aview SEGS _ _ _ _ _ (KIMG LA_NUL Hi Hns Her Hgn)).
  pose proof (HNUL k Hk) as X.
  replace (LA_NUL + Z.of_nat k) with LA_NUL in X by lia. exact X. }
(* apply the next phase *)
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdF := mdx) end.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  apply (HNEXT cx fx fp 0 (c_ly cx) S2 (c_W cx) msx mdF HB0 BoxBase.fxr_refl HJ3 Hfrs2) end.
(* ---- lf_gl_inv 0 ---- *)
assert (EFF : lf_F cx fp = F) by reflexivity.
assert (EFL : lf_FL cx fp = FL) by reflexivity.
assert (ESH2 : lf_SH cx fp = SH) by reflexivity.
assert (ESP1 : lf_sp1 cx = sp1) by reflexivity.
unfold lf_gl_inv, lf_setup_inv, lf_shape, lf_core, lf_saved, lf_header, lf_fshadow, lf_cur, lf_slot, lf_at.
rewrite ?EFF, ?EFL, ?ESH2, ?ESP1.
cbn [ms_regs ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
exists (repeat (Z_to_bv 8 0) (Z.to_nat NK_SIZE)).
assert (Hkl : Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat NK_SIZE))) = NK_SIZE)
  by (rewrite repeat_length; unfold NK_SIZE; lia).
assert (Hkn : forall i, (i < length (repeat (Z_to_bv 8 0) (Z.to_nat NK_SIZE)))%nat ->
  nth_error (repeat (Z_to_bv 8 0) (Z.to_nat NK_SIZE)) i = Some (Z_to_bv 8 0))
  by (intros i Hi; apply lf_nth_repeat; rewrite repeat_length in Hi; exact Hi).
split; [lia | split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [| ]]]]]]]]]]]]]]].
all: cbn [ms_regs ms_mem mkst].
- (* lf_setup_inv *)
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [| ]]]]]]]]]]]]]]]]]]]].
  + (* lf_shape *) repeat split; reflexivity.
  + (* lf_core *) cbn [ms_regs ms_mem mkst]. rewrite ?ESP1.
    split; [rewrite Q2; rewrite E4_60; reflexivity|].
    split; [rewrite Q8; rewrite (EEcut 2%nat 2%bv eq_refl ltac:(lia)); unfold spZ, w64;
            rewrite ?Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q9; rewrite E4_60; reflexivity|].
    split; [rewrite Q3; exact (EEcut 3%nat 3%bv eq_refl ltac:(lia))
           |rewrite Q4; exact (EEcut 4%nat 4%bv eq_refl ltac:(lia))].
  + (* lf_saved *)
    destruct (lf_saved_of E4v (w_H (c_W cx)) (ms_mem msG) (spZ (c_regs cx)) (c_regs cx) _ _ _ _ _
      HRst U4_2 ltac:(intros nn r Hn; apply (EEcut nn r Hn);
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; lia)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)) as [HSV1 HSV2].
    exact (conj HSV1 HSV2).
  + (* lf_header *) rewrite ?EFF, ?EFL. split; [|split; [|split]].
    * rewrite <- (Z.add_0_r F). lf_rd HRf U4_44 0. { reflexivity. } { unfold LF_MAGIC; lia. }
    * lf_rd HRf U4_44 8. { cbn [sv_denot]. rewrite EO3, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      { unfold LA_DESCR; lia. }
    * lf_rd HRf U4_44 16. { cbn [sv_denot]. rewrite EO4, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      { unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; lia. }
    * rewrite (proj1 LF_frame_slot). replace (F + 1024 - 8) with (F + 1016) by lia.
      lf_rd HRf U4_44 1016. { cbn [sv_denot]. rewrite E4_61, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      { unfold in_app in HFLapp; lia. }
  + (* lf_fshadow *) rewrite ?ESH2.
    exact (lf_shadow_bytes E4v _ _ 62%nat SH _ _ _ _ _ LF_SH0 HRsh U4_62 ltac:(vm_compute; reflexivity)).
  + (* s3 *) rewrite ?ESH2. rewrite Q19, OLD4 by lia. rewrite E62. reflexivity.
  + rewrite ?ESP1. lf_rd HRs1 U4_60 LS_SHB.
    { cbn [sv_denot]. rewrite E4_32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    { unfold SHADOW_OFF; lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_FK.
    { cbn [sv_denot]. rewrite E4_44, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } { lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_F.
    { cbn [sv_denot]. rewrite E4_44, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } { lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_F0.
    { cbn [sv_denot]. rewrite E4_44, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } { lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_WA.
    { cbn [sv_denot]. rewrite E4_44, unsigned_lit_small by lia. reflexivity. } { unfold LO_WA; lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_B160.
    { cbn [sv_denot]. rewrite E4_44, unsigned_lit_small by lia. reflexivity. } { unfold LO_B160; lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_B1A0.
    { cbn [sv_denot]. rewrite E4_44, unsigned_lit_small by lia. reflexivity. } { unfold LO_B1A0; lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_B2E0.
    { cbn [sv_denot]. rewrite E4_44, unsigned_lit_small by lia. reflexivity. } { unfold LO_B2E0; lia. }
  + rewrite ?ESP1, ?EFF. lf_rd HRs1 U4_60 LS_B330.
    { cbn [sv_denot]. rewrite E4_44, unsigned_lit_small by lia. reflexivity. } { unfold LO_B330; lia. }
  + (* lf_cur *) rewrite ?ESP1. split; [|split].
    * lf_rd HRs1 U4_60 LS_P.
      { cbn [sv_denot]. rewrite E4_10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      { destruct Hpn as [[_ Hpe] | [Hn Hin]];
          [rewrite Hpe; unfold A_EMPTY; lia
          | destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR Hin) as (Hm0 & Hb & Hc & _);
            pose proof (req_size_pos (c_n cx) ltac:(lia)) as (Hq1 & Hq2);
            unfold alloc_ceiling in *; lia]. }
    * lf_rd HRs1 U4_60 LS_N.
      { cbn [sv_denot]. rewrite E4_11, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } { lia. }
    * exists 0. split; [lia | split; lia].
  + (* lf_jbk *)
    cbn [ms_regs ms_mem mkst].
    split; [lia|]. split; [lia|]. split; [intros c q; reflexivity|].
    split; [rewrite Hfr0; exact Hnin|].
    assert (HFD : m_fds mdF = m_fds (c_md cx) /\ m_fs mdF = m_fs (c_md cx)).
    { unfold mdF. split;
      repeat first [ rewrite (proj1 (wvb_fds_fs _ _ _)) | rewrite (proj2 (wvb_fds_fs _ _ _))
                   | rewrite (proj1 (lf_sbm_fds _ _ Hsame3)) | rewrite (proj2 (lf_sbm_fds _ _ Hsame3))
                   | rewrite (proj1 (lf_sbm_fds _ _ Hsame2)) | rewrite (proj2 (lf_sbm_fds _ _ Hsame2)) ];
      reflexivity. }
    split; [exact (proj1 HFD)|]. split; [exact (proj2 HFD)|].
    split; [destruct HES2 as (f & Hf); rewrite Hf; apply (mo_le_set_fs_r MT MFSL);
            exact (mo_le_refl MT HML (c_S cx))|].
    split; [destruct HES2 as (f & Hf); rewrite Hf; cbn [st_depot set_fs]; lia|].
    split; [ (* amf_gi *)
      apply (amf_gi_frame _ _ (rdW (c_W cx) (c_mem cx)) (rdW (c_W cx) (ms_mem msG)) (c_T cx));
      [ intros a Ha; rewrite HMS in Ha; destruct (lf_amf_facts a (or_introl Ha)) as (Hi & Hns & Her & Hgn);
        exact (mbyte_of_aview SEGS _ _ _ _ _ (KIMG a Hi Hns Her Hgn))
      | intros f x Hf Hx; apply (mbyte_of_aview SEGS);
        replace x with (f + (x - f)) by lia; apply (KBLK f AMF_BLOCK);
        [ exact (HTincl _ Hf)
        | assert (RQ : req_size AMF_BLOCK = AMF_BLOCK) by (vm_compute; reflexivity);
          rewrite ?RQ; unfold AMF_BLOCK, AMF_ZEROED in *; lia ]
      | exact HGI ] |].
    split; [ (* amf_env *)
      apply (amf_env_frame _ _ (rdW (c_W cx) (c_mem cx)) (rdW (c_W cx) (ms_mem msG)));
      [ intros a Ha; rewrite HMS in Ha; destruct (lf_amf_facts a (or_intror Ha)) as (Hi & Hns & Her & Hgn);
        exact (mbyte_of_aview SEGS _ _ _ _ _ (KIMG a Hi Hns Her Hgn))
      | exact HENV ] |].
    split; [ (* lf_bl *) exists []; split; [rewrite app_nil_r; reflexivity|];
             rewrite Eab; cbn [app]; apply Permutation_refl |].
    split; [rewrite Eab; exact HTincl|].
    split; [exact HNULc|].
    split; [exact HRODc|].
    split; [ (* the payload *)
      assert (HG : garr8 SEGS (rdW (c_W cx) (ms_mem msG)) (c_p cx)
                     (map (fun b : byte => bv_unsigned b) (c_pl cx)))
        by (apply (garr8_frame SEGS (rdW (c_W cx) (c_mem cx)) (rdW (c_W cx) (ms_mem msG)) _ _ HPL);
            intros a Ha; rewrite length_map in Ha; apply (mbyte_of_aview SEGS);
            replace a with (c_p cx + (a - c_p cx)) by lia; apply KIN; lia);
      split; [ destruct Hpn as [[_ Hpe] | [Hn Hin]];
                 [rewrite Hpe; unfold A_EMPTY; lia
                 | destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR Hin) as (Hm0 & Hb & _); lia ] |];
      split; [ destruct Hpn as [[Hn0 Hpe] | [Hn Hin]];
                 [ rewrite Hpe; assert (length (c_pl cx) = 0%nat) by lia; unfold A_EMPTY; lia
                 | destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR Hin) as (Hm0 & Hb & Hc & _);
                   unfold req_size, alloc_ceiling in *;
                   destruct (Z.eqb_spec (c_n cx) 0) as [Hq|Hq]; lia ] |];
      intros i Hi; cbn [ms_regs ms_mem mkst];
      rewrite (garr8_mbyte SEGS (rdW (c_W cx) (ms_mem msG)) _ _ i HG ltac:(rewrite length_map; exact Hi));
      rewrite (nth_error_nth' (c_pl cx) (Z_to_bv 8 0) Hi); f_equal;
      change 0 with (bv_unsigned (Z_to_bv 8 0)) at 1;
      rewrite (map_nth (fun b : byte => bv_unsigned b) (c_pl cx) (Z_to_bv 8 0) i);
      apply Z_to_bv_bv_unsigned |].
    exact KIN.
  + exact (lf_gnames_w_holds _).
  + exact (lf_odd_at_holds _ HRODc).
  + exact (lf_texts_at_holds _ HRODc).
  + apply lf_la_at_holds. unfold LA_NUL in HNULc. rewrite Hlanul in HNULc. exact HNULc.
- (* s2 = g_nl *) rewrite Q18, EO2. reflexivity.
- (* s5 = g_names *) rewrite Q21, EO5. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
- (* s6 = .str *) rewrite Q22, EO6. reflexivity.
- (* s7 = 64 *) rewrite Q23. reflexivity.
- (* s8 = 2 *) rewrite Q24. reflexivity.
- (* s9 *) rewrite Q25. reflexivity.
- (* s10 = g_nl + 0x42000 *) rewrite Q26. cbn [sv_denot]. rewrite UO2. reflexivity.
- (* s11 *) rewrite Q27. reflexivity.
- (* anlk_at *)
  split; [split|exact Hkl].
  + split; [unfold LA_G_NL; lia|]. split; [rewrite Hkl; unfold LA_G_NL, NK_SIZE; lia|].
    intros i Hi. rewrite (Hkn i Hi). apply HGZ. rewrite repeat_length in Hi. unfold NK_SIZE in *. lia.
  + intros k Hk. rewrite Hkl in Hk. unfold NK_SIZE in Hk.
    pose proof (LA_G_NL_writable (rdW (c_W cx) (ms_mem msG)) (LA_G_NL + k) ltac:(lia)) as Hw.
    rewrite <- HSEGS in Hw. exact Hw.
- (* nk_n_if = 0 *)
  change (0 - 0 / 16) with 0. unfold lf_tab_at. cbn [Z.to_nat firstn length Z.of_nat].
  unfold nk_n_if, fld_u32. apply lf_rdn4_zero; [exact Hkn | unfold NK_N_IF; lia |].
  rewrite Hkl. unfold NK_N_IF, NK_SIZE. lia.
- (* aiftab_at *)
  replace (lf_tab_at (0 - 0 / 16)) with (@nil (list byte * Z)) by reflexivity.
  split; [|split].
  + unfold nk_n_if, fld_u32. rewrite (lf_rdn4_zero _ NK_N_IF Hkn ltac:(unfold NK_N_IF; lia)
      ltac:(rewrite Hkl; unfold NK_N_IF, NK_SIZE; lia)). reflexivity.
  + cbn. lia.
  + intros i nm ix Hnth. destruct i; discriminate Hnth.
- (* lf_ifp *) change (0 - 0 / 16) with 0. intros e He. lia.
- (* g_nl is zero outside the table's fields *)
  intros q Hq _ _ _ k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
  replace (LA_G_NL + q + Z.of_nat 0) with (LA_G_NL + q) by lia.
  rewrite (HGZ q Hq). f_equal; f_equal; unfold YG0f.le_byte;
  rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l; reflexivity.
- (* lf_gnames_at 0 *) intros k Hk. lia.
Qed.

End b.
End a.
