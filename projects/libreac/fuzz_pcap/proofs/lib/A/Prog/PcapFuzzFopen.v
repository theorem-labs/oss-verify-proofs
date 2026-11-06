From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Modified by Theorem Labs, 2026-10: taken from a working branch d2efa2b83ff without its uncommitted DRAFT_fopen.v (sha256 c5819f1f77c8; internal record): the image facts (segments, read-only image) and the strcmp wrapper's contract are named Section hypotheses; the strcmp window is FO_WIN's ESTACK. *)
(* Modified by Theorem Labs, 2026-10: roimg_low, roimg_kept_aview, astrcmp_path_at and the Record FopenImg (fields fi_sep / fi_head / fi_kimg, their Arguments lines, and FopenImg's clear-implicits line with its guard) moved unchanged to the image-free PcapFuzzFopenG.v, which this file Requires by Export, so that both images' walks can use one text; lib/B/Prog/PcapFuzzFopen.v (a working branch a629513d834) still restates them and does not Require PcapFuzzFopenG.v. Their implicit arguments outside that file's Section are the ones this file's users saw before: so the hypothesis FI names SK (here the Section's, the same term), and the proof reads the fields as fi_sep _ _ _ FI (the fields' Arguments lines act only inside the Section). *)
(* libreac_fuzz_fopen (fuzz_pcap.asan v1.9.0, 0x80738, 36 instructions): the contract of the ASan build's code in
   cgif_file's per-function form, and its walk over the position-abstract listing.
   The function takes a 32-byte frame, saves ra, s0 (the mode) and s1 (the path), calls the strcmp wrapper on the path
   and the "<fuzz-input>" literal, and on equality loads the 8-byte word stored in the global g_file_len (the input's
   length n): when n is 0 it returns 0 without any call (0x80788 `ld a1,0x7bc(a0)`, 0x8078c `beqz a1,0x807b0`,
   0x807b0 `li a0,0` ... `ret`), and that empty input is the only way it returns 0; otherwise it loads the 8-byte word
   stored in the global g_file (the input buffer's address b), pops its frame and tail-jumps to the fmemopen wrapper
   (0x807ac `j 0x415c4`) with a0 = b and a1 = n (the two globals' contents, not their addresses) and a2 = the mode, so
   the wrapper returns to this function's caller with the new stream. The NULL-path branch (0x80750) and the
   strcmp-unequal branch (0x80764, a tail jump to the fopen wrapper) are not reached: the path is the literal, and
   strcmp returns 0 on it. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0s YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0s YC5d PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSyms PcapList PcapPa PcapAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapPaLib PcapBase PcapFrame YC4b YC1g YC85.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapFuzzFopenG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The listing's objects this function names (PcapAddr.v): the "<fuzz-input>" literal, g_file_len and g_file. *)
Definition FO_PATH : nat := 3%nat.
Definition FO_LEN : nat := 4%nat.
Definition FO_FILE : nat := 2%nat.
Definition SB_FO : Z := 0x7fff8000.
Definition Bx_FO : sv := SLit SB_FO.
Definition Bspan_FO : Z * Z := (SB_FO, SB_FO + 2 ^ 44 - 1).

(* The symbolic state at the entry: the frame below sp, and the two globals, whose values are the atoms 32 (the
   length) and 33 (the buffer). *)
Definition fo_regions0 : smem :=
[ stack_region 32; obj8_region FO_LEN (SOff 32 0); obj8_region FO_FILE (SOff 33 0) ].
Definition ss_fo0 : sstate :=
mkSS AF_libreac_fuzz_fopen sr_atoms fo_regions0 None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section f.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition A_libreac_fuzz_fopenP : Z := BASE + AF_libreac_fuzz_fopen.
Section h.
Variable B : asyms.
Variable K : asource_syms.
(* The return address of the malloc call inside the C library's fmemopen (afmemopen_spec's ra), and the call
   spines this function may be called under (afmemopen_spec's CTX: fmemopen's malloc records the caller's spine,
   because the tail jump leaves s0 the caller's frame pointer). *)
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable MT : ameter_ops.
(* The read-only-image fact the statement takes as roimg (lib/A instantiates it with a Theorem Labs lane's ro_img, AE3i.v), and
   that it depends only on the bytes below alloc_ceiling (a Theorem Labs lane discharges ROIMG_LOW for ro_img: its region
   [IMG_RO_LO, IMG_RO_HI) lies below alloc_ceiling and has no writable part, YI04.region_ok_transport). *)
Variable roimg : (word -> option byte) -> Prop.
Hypothesis ROIMG_LOW : roimg_low SEGS roimg.
(* The word-constant window afmemopen_spec asks for, and the fact that the read-only-image fact pins it; the lib/A
   top discharges MCONSTS for roimg := ro_img at mc_lo := 0x10350, mc_hi := 0x10370 from AE3i's chunk
   0x10330 .. 0x10398 (a Theorem Labs lane; the chunk is unchanged in the regenerated table) and SEGS = tfibsegs (AB1v). *)
Variables mc_lo mc_hi : Z.
Hypothesis MCONSTS : forall (W : world SEGS) (mem : word -> option byte), roimg (rdW W mem) ->
  forall a, mc_lo <= a < mc_hi ->
  aview SEGS (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a)).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MLAWS : ameter_laws MT.
Hypothesis FI : FopenImg SK (VAL (A_OBJ FO_LEN)) (VAL (A_OBJ FO_FILE)) K.
(* The strcmp wrapper's contract at the listing's strcmp trampoline and object FO_PATH; the lib/A top discharges it
   from a Theorem Labs lane's astrcmp_lit_realizes B with SEGS = tfibsegs (a Theorem Labs lane's AB1v), roimg = ro_img (AE3i),
   pcap_sigma PS___interceptor_trampoline_strcmp = SM_ENTRY and pcap_obj FO_PATH = A_FUZZ_PATH (StrcmpDef.v). *)
Hypothesis STRCMP : astrcmp_path_at SEGS B roimg (SIGMA PS___interceptor_trampoline_strcmp) (VAL (A_OBJ FO_PATH)).
Hypothesis AFMEMOPEN : afmemopen_spec SK SEGS B K MT CTX (SIGMA PS___interceptor_trampoline_fmemopen) FM_RA
  mc_lo mc_hi.
Let RUN := paj_run (SK := SK) B LAWS.
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let BR := paj_branch (PI := PI).
Lemma ew_imgP : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma base_obj : forall E i, img_env VAL A_LIM E -> (i < 17)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i).
Proof. intros E i HE Hi. cbn [base_val]. apply HE. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
(* The call of the strcmp wrapper, as a journal step: the wrapper writes only inside the ESTACK window below
   the caller's sp, and returns 0 on the two equal literals. *)
Lemma aj_strcmp_at : forall W (regsc : bvmap 5 word) memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
getr regsc 10 = w64 (VAL (A_OBJ FO_PATH)) -> getr regsc 11 = w64 (VAL (A_OBJ FO_PATH)) ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw ->
roimg (rdW W memc) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ FO_PATH)) 13 ->
shadow_hull_vis (aview SEGS (w_H W) memc) (VAL (A_OBJ FO_PATH)) 13 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_strcmp)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsc regs2 /\ getr regs2 10 = w64 0 /\ same_but_materialized mdc md2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Ha0 Ha1 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HRO HRA HHV.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsc memc mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc o);
  [ exact HJ | exact Hsp | exact Hal | exact Hneg | exact Hbud | rewrite Hra; exact Hraw | exact Hgp | exact Htp ]. }
eapply SRr_mono.
{ change (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_strcmp)) memc (seg_rom SEGS)) mdc)
    with (cfg_at SEGS (SIGMA PS___interceptor_trampoline_strcmp) regsc memc mdc).
  exact (STRCMP lyc Sc W regsc memc mdc HPRE Ha0 Ha1 HRO HRA HHV). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & Hres & Heff & Hpres2).
rewrite Hsp in Heff.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply Heff; [exact Ha | exact Hna].
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha. left. left. lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT). exact HQT. }
split; [exact HP2|]. split; [exact Hres|]. split; [exact Hsame|]. split; [exact Heff | exact Hpres2].
Qed.
Lemma fo_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch n b,
afn_pre SEGS B LIBREAC_FUZZ_FOPEN_STK ly S W regs mem md ch ->
val_mem SEGS (rdW W mem) (VAL (A_OBJ FO_LEN)) 8 n -> 0 <= n < 2 ^ 64 ->
val_mem SEGS (rdW W mem) (VAL (A_OBJ FO_FILE)) 8 b -> 0 <= b < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])) ss_fo0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_libreac_fuzz_fopen)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_FO [] (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch n b HPRE Vn Rn Vb Rb. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (fi_sep _ _ _ FI) as Hsep.
pose proof (pa_obj_img FO_LEN ltac:(unfold FO_LEN; lia)) as Hol.
pose proof (pa_obj_img FO_FILE ltac:(unfold FO_FILE; lia)) as Hof.
unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
set (E := Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 n)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 1)).
pose proof (base_obj E FO_LEN HEI ltac:(unfold FO_LEN; lia)) as BL.
pose proof (base_obj E FO_FILE HEI ltac:(unfold FO_FILE; lia)) as BF.
rewrite restrict_mkst_fx. unfold ss_fo0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold fo_regions0, stack_region, obj8_region. fold E.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK in *. lia.
+ rewrite BL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ FO_LEN)) 0 8 (SOff 32 0) n);
[ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vn ].
+ rewrite BF. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ FO_FILE)) 0 8 (SOff 33 0) b);
[ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vb ].
- apply pairwise_disjoint_of_extents. unfold fo_regions0, stack_region, obj8_region, extent_of_region. fold E.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BL, BF. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK in *. unfold ESTACK in *. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.

Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msy) => pose proof (st_ok_restrict_reg sg Hh Ex ssx msy r HS) as Hr
| st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msy) => pose proof (st_ok_pi_restrict_reg Hh Ex ssx msy r HS) as Hr
end;
lazymatch type of Hr with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Hr end;
cbn [ms_regs restrict mkst] in Hr.

Ltac fo_win_tac Usp :=
intros bb wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; unfold FO_WIN, ESTACK; lia|]);
destruct Hin.
Theorem pb_libreac_fuzz_fopenX :
  tlibreac_fuzz_fopen_specX SK SEGS A_libreac_fuzz_fopenP (VAL (A_OBJ FO_PATH)) (VAL (A_OBJ FO_LEN))
    (VAL (A_OBJ FO_FILE)) roimg B K MT FM_RA CTX.
Proof.
unfold tlibreac_fuzz_fopen_specX.
intros ly S W regs mem md ch n b C HPRE HCTX H10 H11 HRO HRA HHV Vn Vb Rb HNONE HnC Hn26 HBLK Hev Hlive HMO HU1 HU2.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Rn : 0 <= n < 2 ^ 64) by (rewrite HnC; lia).
destruct (fo_entry ly S W regs mem md ch n b HPRE Vn Rn Vb Rb) as [HS SHOK].
pose proof (ajournal_init SEGS B LIBREAC_FUZZ_FOPEN_STK afmemopen_fp ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LIBREAC_FUZZ_FOPEN_STK = 18624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (pa_obj_img FO_PATH ltac:(unfold FO_PATH; lia)) as Hop.
pose proof (pa_obj_img FO_LEN ltac:(unfold FO_LEN; lia)) as Hol.
pose proof (pa_obj_img FO_FILE ltac:(unfold FO_FILE; lia)) as Hof.
unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in Hop, Hol, Hof.
assert (HLO : alloc_ceiling <= spZ regs - 32 - ESTACK) by lia.
remember (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 1)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b]) E) by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at, A_libreac_fuzz_fopenP.
change (w64 (BASE + AF_libreac_fuzz_fopen)) with (Z_to_bv 64 (BASE + AF_libreac_fuzz_fopen)).
(* 0x80738 .. 0x80750: the frame, the saves of ra / s0 / s1, and the test of the path against NULL. *)
paj_run_tok RUN HS HJ SHOK Bspan_FO; [awr_ok_tac; exact Usp |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp)) as KF1.
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hna; exact (KF1 a Ha Hna)) end.
clear KF1.
psrr_branch_tok RUN BR HS SHOK Bspan_FO.
- (* 0x80750 taken: the path would be NULL, but it is the image's literal. *)
  exfalso. rewrite branch_eq_U in Hc.
  assert (U10 : U E (SOff 10 0) = VAL (A_OBJ FO_PATH))
    by (apply U_atom; [rewrite E10, H10; reflexivity | pose proof (pa_val_range (A_OBJ FO_PATH)); lia]).
  assert (U0 : U E (SLit 0) = 0) by reflexivity.
  rewrite U10, U0 in Hc. apply Z.eqb_eq in Hc. lia.
- (* 0x80754 .. 0x80760: the literal's address and the call of the strcmp wrapper. *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan_FO; [awr_ok_tac; exact Usp |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp)) as KF2.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                  aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hna; rewrite (KF2 a Ha Hna); exact (UN a Ha Hna)) end.
  clear KF2 UN. rename UN2 into UN.
  pmkst HS.
  preg HS (1%bv : bv 5) Rra. preg HS (2%bv : bv 5) Rsp. preg HS (3%bv : bv 5) Rgp.
  preg HS (4%bv : bv 5) Rtp. preg HS (10%bv : bv 5) Ra0. preg HS (11%bv : bv 5) Ra1.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    assert (Ha0 : getr rg 10 = w64 (VAL (A_OBJ FO_PATH)))
      by (rewrite Ra0; apply (sv_off0 E 10); rewrite E10; exact H10);
    assert (Ha1 : getr rg 11 = w64 (VAL (A_OBJ FO_PATH)))
      by (rewrite Ra1; apply (sv_off0 E (A_OBJ FO_PATH));
          apply (ew_imgP E (A_OBJ FO_PATH) HEI); unfold A_OBJ, A_TEXT, A_LIM, FO_PATH; lia);
    assert (Hgp2 : getr rg 3 = w64 (as_gp B)) by (rewrite Rgp; apply (sv_off0 E 3); rewrite E3; exact Hgp);
    assert (Htp2 : getr rg 4 = w64 (as_tp B)) by (rewrite Rtp; apply (sv_off0 E 4); rewrite E4; exact Htp);
    assert (Hra2 : getr rg 1 = Z_to_bv 64 (BASE + 44))
      by (rewrite Rra; exact (codeptr_val E 44 HEI));
    assert (Qsp : spZ rg = spZ regs + -32)
      by (unfold spZ at 1; rewrite Rsp; cbn [sv_denot]; rewrite Usp, unsigned_lit_small by lia; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    assert (FD1 : m_fds mdx = m_fds md /\ m_fs mdx = m_fs md)
      by (rewrite ?md_fds_wvb, ?md_fs_wvb; split; reflexivity) end.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (aj_strcmp_at W rg mm LIBREAC_FUZZ_FOPEN_STK (spZ regs) afmemopen_fp ly S W mem md []
                ly S mdx 0 (-32) (Z_to_bv 64 (BASE + 44)));
      [ exact HJ | exact Ha0 | exact Ha1 | exact Qsp | reflexivity | lia | lia | exact Hgp2 | exact Htp2
      | exact Hra2 | apply ret_ok_codeptr_v; [lia | reflexivity]
      | exact (roimg_kept_aview SEGS roimg ROIMG_LOW W mem mm (spZ regs) UN HLO HRO)
      | eapply (range_addressable_kept_win _ _ (spZ regs - 32 - ESTACK) (spZ regs));
        [ intros s Hs Hns; apply UN; [exact Hs | unfold FO_WIN; exact Hns] | lia | lia | lia | exact HRA ]
      | eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 32 - ESTACK) (spZ regs));
        [ intros s Hs Hns; apply UN; [exact Hs | unfold FO_WIN; exact Hns] | lia | lia | lia | lia | exact HHV ] ]
    end. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hsm2 & Heff & Hpres2).
  assert (FD2 : m_fds md2 = m_fds md /\ m_fs md2 = m_fs md)
    by (destruct (sbm_fds _ _ Hsm2) as [G1 G2]; rewrite G1, G2; exact FD1).
  clear Hsm2 FD1.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hna. rewrite (Heff a Ha ltac:(unfold FO_WIN in Hna; lia)). apply UN; [exact Ha | exact Hna]. }
  (* the state at the return of the strcmp wrapper: its own frame and the two globals are kept. *)
  jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    assert (OBL : bv_unsigned (ew E 245%nat) = VAL (A_OBJ FO_LEN)) by (apply (HEI 245%nat); unfold A_TEXT, A_LIM; lia).
    assert (OBF : bv_unsigned (ew E 243%nat) = VAL (A_OBJ FO_FILE)) by (apply (HEI 243%nat); unfold A_TEXT, A_LIM; lia).
    repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
    - apply (mbyte_of_aview SEGS). apply Heff; rewrite Usp in Ha; lia.
    - intros _. apply (apresent_writable SEGS). apply HJpres. rewrite Usp in Ha. lia.
    - rewrite OBL in Ha. apply (mbyte_of_aview SEGS). apply Heff; lia.
    - exfalso. lia.
    - rewrite OBF in Ha. apply (mbyte_of_aview SEGS). apply Heff; lia.
    - exfalso. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 34 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD : forall k, (k < 34)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
  assert (HAE' : env_agree 32 (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b]) E')
    by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HE'.
  assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
  assert (F2 : ew E' 2 = getr regs 2) by (rewrite OLD by lia; exact E2).
  assert (F3 : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
  assert (F4 : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
  assert (F8 : ew E' 8 = getr regs 8) by (rewrite OLD by lia; exact E8).
  assert (F11 : ew E' 11 = getr regs 11) by (rewrite OLD by lia; exact E11).
  assert (F32 : ew E' 32 = Z_to_bv 64 n) by (rewrite OLD by lia; exact E32).
  assert (F33 : ew E' 33 = Z_to_bv 64 b) by (rewrite OLD by lia; exact E33).
  assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite F2; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  assert (SHOK' : sh_ok SEGS Bx_FO [] E' (mrestrict (w_H W) mem2)) by constructor.
  clear SHOK.
  (* strcmp returned 0, so the branch at 0x80764 is taken. *)
  assert (HS' := HS).
  apply (st_ok_pi_pin_reg' E' _ _ (10%bv : bv 5) 0) in HS';
    [| cbn [ms_regs restrict mkst]; exact Hres | reflexivity].
  lazymatch type of HS' with st_ok_pi _ _ _ ?ss4 _ => let v := eval vm_compute in ss4 in change ss4 with v in HS' end.
  clear HS. rename HS' into HS.
  (* 0x80764 .. 0x8078c: the equal path, the read of g_file_len, and the test of the length. *)
  paj_run_tok RUN HS HJ2 SHOK' Bspan_FO; [awr_ok_tac; exact Usp' |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp')) as KF3.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (UN4 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                  aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hna; rewrite (KF3 a Ha Hna); exact (UN3 a Ha Hna)) end.
  clear KF3.
  psrr_branch_tok RUN BR HS SHOK' Bspan_FO.
  + (* 0x8078c taken: the length is 0; 0x807b0 returns 0 with no call and no allocation. *)
    rewrite branch_eq_U in Hc.
    assert (Un : U E' (SOff 32 0) = n) by (apply U_atom; [exact F32 | lia]).
    assert (U0 : U E' (SLit 0) = 0) by reflexivity.
    rewrite Un, U0 in Hc. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ2 SHOK' Bspan_FO; [awr_ok_tac; exact Usp' |].
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp')) as KF4.
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                    aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (KF4 a Ha Hna); exact (UN4 a Ha Hna)) end.
    clear KF4.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      preg HS (1%bv : bv 5) R1; preg HS (10%bv : bv 5) R10;
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros mat';
      unfold tlibreac_fuzz_fopen_post, apost_base;
      exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
      split; [cbn [ms_regs]; rewrite R1, (sv_off0 E' 1 _ F1), Hra; reflexivity|];
      split; [eapply (ajournal_mono_k SEGS B);
              [eapply ajournal_materialize; (try exact LAWS); (try exact Hsegs); exact HJ2
              | unfold EV_FUZZ_FOPEN; lia]|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [Z_to_bv 64 n; Z_to_bv 64 b] HS);
              [exact HAE' | vm_compute; reflexivity]|];
      exists 0;
      split; [cbn [ms_regs]; rewrite R10; reflexivity|];
      split; [reflexivity|];
      split; [rewrite ?md_fds_wvb; exact (proj1 FD2)|];
      split; [rewrite ?md_fs_wvb; exact (proj2 FD2)|];
      split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split;
              [eapply (asource_none_kept SEGS K W mem (ms_mem msc) (spZ regs)); [exact (fi_kimg _ _ _ FI) | exact UN5 | exact HLO | exact HNONE]
              | exact (mo_le_refl MT MLAWS S)]|];
      intros Hge; exfalso; lia
    end.
  + (* 0x80790 .. 0x807ac: the length is not 0; the tail jump to the fmemopen wrapper. *)
    rewrite branch_eq_U in Hc.
    assert (Un : U E' (SOff 32 0) = n) by (apply U_atom; [exact F32 | lia]).
    assert (U0 : U E' (SLit 0) = 0) by reflexivity.
    rewrite Un, U0 in Hc. apply Z.eqb_neq in Hc.
    assert (Hn1 : 1 <= n) by lia.
    destruct (HBLK Hn1) as (Hinb & Hgarr & Hbytes).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hinb) as (Hb16 & Hb4096 & Hbceil & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
    paj_run_tok RUN HS HJ2 SHOK' Bspan_FO; [awr_ok_tac; exact Usp' |].
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp')) as KF4.
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                    aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (KF4 a Ha Hna); exact (UN4 a Ha Hna)) end.
    clear KF4.
    pmkst HS.
    preg HS (1%bv : bv 5) Tra. preg HS (2%bv : bv 5) Tsp. preg HS (3%bv : bv 5) Tgp.
    preg HS (4%bv : bv 5) Ttp. preg HS (8%bv : bv 5) Ts0.
    preg HS (10%bv : bv 5) Ta0. preg HS (11%bv : bv 5) Ta1. preg HS (12%bv : bv 5) Ta2.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      assert (Ta0' : getr rg 10 = w64 b) by (rewrite Ta0; apply (sv_off0 E' 33); exact F33);
      assert (Ta1' : getr rg 11 = w64 n) by (rewrite Ta1; apply (sv_off0 E' 32); exact F32);
      assert (Ta2' : getr rg 12 = w64 (as_mode K)) by (rewrite Ta2; apply (sv_off0 E' 11); rewrite F11; exact H11);
      assert (Tgp' : getr rg 3 = w64 (as_gp B)) by (rewrite Tgp; apply (sv_off0 E' 3); rewrite F3; exact Hgp);
      assert (Ttp' : getr rg 4 = w64 (as_tp B)) by (rewrite Ttp; apply (sv_off0 E' 4); rewrite F4; exact Htp);
      assert (Tra' : getr rg 1 = getr regs 1) by (rewrite Tra; apply (sv_off0 E' 1); exact F1);
      assert (Tsp' : spZ rg = spZ regs + 0)
        by (unfold spZ at 1; rewrite Tsp, (sv_off0 E' 2 _ F2); unfold spZ; lia);
      assert (Ts0' : s0Z rg = s0Z regs)
        by (unfold s0Z at 1; rewrite Ts0; rewrite (sv_off0 E' 8 _ F8); reflexivity)
    end.
    eapply SRr_mono.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
        eapply (cl_callS B LAWS W rg mm (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_fmemopen))
                  LIBREAC_FUZZ_FOPEN_STK (spZ regs) afmemopen_fp ly S W mem md [] ly S mdx 0
                  AFMEMOPEN_STK afmemopen_fp 1 0 (getr regs 1) ch
                  (fun ly2 S2 W2 regs2' mem2' md2' => exists res : Z,
                     getr regs2' 10 = w64 res /\ frames S2 = frames S /\
                     mo_le MT S S2 (mo_malloc MT SRC_FILE_BLOCK) /\
                     m_fds md2' = m_fds md /\ m_fs md2' = m_fs md /\
                     4096 <= res /\ res mod 16 = 0 /\
                     ablocks B ly2 S2 = ablocks B ly S ++ [(res, SRC_FILE_BLOCK)] /\
                     asource_unbuffered SEGS K (rdW W2 mem2') res b C 0))
      end.
      all: try exact HJ2. all: try exact Tsp'. all: try exact Tgp'. all: try exact Ttp'.
      all: try exact Tra'. all: try exact Hra. all: try exact Hra4.
      all: try reflexivity. all: try lia.
      all: try (cbv [LIBREAC_FUZZ_FOPEN_STK AFMEMOPEN_STK]; lia).
      - rewrite Z.add_0_r. rewrite Ts0'.
        eapply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
        intros a Ha. apply UN5; [lia | unfold FO_WIN; lia].
      - intros HPREc.
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
          eapply SRr_mono;
          [ exact (AFMEMOPEN W ly S rg mm mdx ch b n C (fi_head _ _ _ FI) HPREc HCTX Ta0' Ta1' Ta2'
                     (asource_none_kept SEGS K W mem mm (spZ regs) (fi_kimg _ _ _ FI) UN5 HLO HNONE) HnC (conj Hn1 Hn26) Hinb
                     (garr8_kept SEGS W mem mm (spZ regs) b C UN5 HLO ltac:(lia) ltac:(lia) Hgarr) Hbytes
                     (MCONSTS W mm (roimg_kept_aview SEGS roimg ROIMG_LOW W mem mm (spZ regs) UN5 HLO HRO))
                     Hev Hlive HMO HU1 HU2)
          | ] end.
        cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hres3 & Hfr3 & Hmle3 & Hfd3 & Hfs3 & Hsucc3).
        exists ly3, S3, regs3, mem3, md3.
        split; [rewrite Tra'; reflexivity|].
        split; [exact HJ3|]. split; [exact HP3|].
        exists res. split; [exact Hres3|]. split; [exact Hfr3|]. split; [exact Hmle3|].
        split; [rewrite Hfd3, ?md_fds_wvb; exact (proj1 FD2)|].
        split; [rewrite Hfs3, ?md_fs_wvb; exact (proj2 FD2)|].
        exact Hsucc3.
      - intros a Ha. left. exact Ha. }
    cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ4 & _ & HP4 & res & Hres4 & Hfr4 & Hmle4 & Hfd4 & Hfs4 & H4096 & H16 & Hbl & Hsrc).
    unfold tlibreac_fuzz_fopen_post, apost_base.
    exists ly3, S3, regs3, mem3, md3.
    split; [reflexivity|].
    split; [rewrite Z.add_0_l in HJ4; exact HJ4|].
    split.
    { eapply aregs_preserved_trans; [|exact HP4].
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ =>
        eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [Z_to_bv 64 n; Z_to_bv 64 b] HS);
        [exact HAE' | vm_compute; reflexivity] end. }
    exists res. split; [exact Hres4|]. split; [exact Hfr4|].
    split; [exact Hfd4|]. split; [exact Hfs4|].
    split; [intros Hz; exfalso; lia|].
    intros _. split; [exact H4096|]. split; [exact H16|]. split; [exact Hbl|]. split; [exact Hsrc | exact Hmle4].
Qed.
End h.
End f.
End d.

(* The address facts the walk's image hypotheses rest on, on the tables fuzz_pcap.asan gives (PcapAddr.v): the
   listing's strcmp trampoline is 0x41564 and its object FO_PATH is the "<fuzz-input>" literal at 0x20d00 (both
   measured on fuzz_pcap.asan v1.9.0's unstripped twin; StrcmpDef.v's SM_ENTRY and A_FUZZ_PATH, which STRCMP's
   discharge equates them with), and the two globals this function reads do not overlap (FopenImg's fi_sep). They
   are checked here so that the hypotheses are known to be satisfiable. *)
Lemma fopen_img_tables :
pcap_sigma PS___interceptor_trampoline_strcmp = (symaddr Symbols.Asan.s___wrap_strcmp) /\
pcap_obj FO_PATH = (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z) /\
(pcap_obj FO_LEN + 8 <= pcap_obj FO_FILE \/ pcap_obj FO_FILE + 8 <= pcap_obj FO_LEN).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. left. vm_compute. discriminate.
Qed.
