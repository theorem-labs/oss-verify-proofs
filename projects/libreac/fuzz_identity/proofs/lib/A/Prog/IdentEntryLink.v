(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the link of fuzz_identity's ASan (image A) entry function to the A closer. *)
(* The A closer is fuzz_grant's lib/A/AGrantT.v relocated to identity. Where AGrantT.v:40 assumes LIBX_ALL, it has the lemma
     ident_lib_all : forall rc, @tfib_lib_contract_x_all rc identity_shape IdentB ameter_triv XL0 XL0 RLO RHI
   with RLO, RHI = 0x9ada0, 0x9d0a8 (pa_relro_lo / pa_relro_hi of PI_ident). This file proves it from the walk's
   theorem LLVMFuzzerTestOneInput_inv.pb_LLVMFuzzerTestOneInput, by one application at the instantiation.

   The relocated core is in this tree: lib/A/ACfn.v, lib/A/AE2k.v and lib/A/IdentTop.v (AGrantT for identity). This file
   states `tfib_lib_contract_x` as a Section copy of fuzz_grant's lib/A/ACfn.v:33-72, 137-139 (the same text but for the
   segment list, RLO' / RHI', ajournal's explicit rc SKi and the YE00 / YE01 names, which are Section variables), and
   `arodata_okS` as a copy of fuzz_grant's YE01.v:190. IdentTop.v:252 (Let LIBX) converts the copy into the core's ACfn.v:72.

   The sink head is PASSED, never inferred: `ident_asan_sink_head` has sk_ofl_head = 0x5f8648, the `ofl_head`
   of fuzz_identity.asan (ofl_lock is 0x5f8640). IdentSkGuard.v
   (required by IdentSyms.v) removes the plain head 0x50640 from resolution, and every use below names the head
   with `@`.

   What this file discharges at the instantiation: HLIBK, HRO, HSTK, HEV, HLIVE, HXM, HXN, HMT0, MTL, MTF (the
   meter is ameter_triv), RO (ro_below_ofl at 0x5f8648, by the image's segment bases), the two image facts of
   reac_box_family_stem (TBLSEP) and reac_box_family_of (HWFIMG, HWFSEP), seg_A (seg_A_holds), and every
   callee contract that has a proved walk on this branch (check_str, reac_box_catalogue,
   reac_box_catalogue_defect, reac_box_family_stem, reac_identity_fw_str, reac_identity_init,
   reac_identity_ingest, reac_box_family_of, reac_identity_reac_ver_str through write_uint, sb_dec, reac_box_name).
   Walks of record: ingest is IngestWalk.pb_reac_identity_ingest;
   sb_dec is sb_decWalk.pb_sb_dec.

   What stays open, by name (Section hypotheses below). The segments: seg_A and the 16 others proved on the
   integration tip (the A entry assembly), seg_D3 and seg_J
   are discharged here from their seg_X_holds: NO segment stays open.
   - the core's runtime contracts: LAWS, TL, TLF, ML, ASM0, ASM3, ASM4, SMP, ASF, FFL, PSIG, AMALLOC4, AFREE4, HUMM,
     HUMF, AMEMSET, AMEMCPY, ABCMP, AMEMCHR, ASTRLEN, ASTRCMP, ASSF5, AJ_NIL_IO, AJ_FP_NIL, ASINK_NONE_KEPT,
     AMETA_INV_KEPT;
   - GM and IV over the CONCRETE globals list G := IDENT_GLOBS (the image's 50 asan_globals descriptors; HWFG, G_HW,
     G_CAT, G_SW, G_IN, G_OUT and G_IMGSTR are proved from it by computation), and ident_himg's image premises HIMG_UNOWNED
     (discharged by lib/A/IdentHimgOwned.v), ZS_STEM, ZS_NAME;
   - every A callee contract is discharged from its walk (put_dec included: HPD_ok);
   - the core's sink names (asink_syms_T, KS, asink_none, ameta_inv) and the record IdentB, as Variables. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO09 YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaTable PaSym IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentImg IdentFrame IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_A
check_str put_dec reac_box_catalogue reac_box_catalogue_defect reac_box_family_of reac_box_family_stem
reac_box_name reac_box_name_walk reac_identity_fw_str reac_identity_init reac_identity_ingest IngestWalk
reac_identity_reac_ver_str write_uint sb_dec sb_decWalk.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
LLVMFuzzerTestOneInput_B LLVMFuzzerTestOneInput_C LLVMFuzzerTestOneInput_D1 LLVMFuzzerTestOneInput_D2 LLVMFuzzerTestOneInput_D3 LLVMFuzzerTestOneInput_D4
LLVMFuzzerTestOneInput_D5 LLVMFuzzerTestOneInput_D6 LLVMFuzzerTestOneInput_Loop LLVMFuzzerTestOneInput_E LLVMFuzzerTestOneInput_F
LLVMFuzzerTestOneInput_G LLVMFuzzerTestOneInput_H LLVMFuzzerTestOneInput_I LLVMFuzzerTestOneInput_J LLVMFuzzerTestOneInput_K LLVMFuzzerTestOneInput_L.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the instantiation ----------------------------------------------------------------------------------- *)
(* fuzz_identity.asan: ofl_head = 0x5f8648 (nm.txt:743). *)
Definition ident_asan_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := 0x5f8648 |}.
Definition A_LLVMF : Z := 0x8070c.
(* the return address of the one call, `jal 8070c` at 0x80604 *)
Definition RA_LLVMF : Z := 0x80608.
Definition A_EMPTY : Z := 0x5d7620.
Definition EV_LIB : Z := 2000.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
Definition XL0 : Z -> Z := fun _ => 0.
Definition RLO : Z := 0x9ada0.
Definition RHI : Z := 0x9d0a8.
Notation identity_shape := Agree.checksum_shape_ag (only parsing).
(* The meter the closer carries: it counts nothing (fuzz_grant's YCbp.v:17-25, with its two law proofs). *)
Definition ameter_triv : ameter_ops :=
{| mo_ok := fun _ _ => True; mo_le := fun _ _ _ => True; mo_malloc := fun _ => 0; mo_free := 0 |}.
Lemma ameter_triv_laws : ameter_laws ameter_triv.
Proof. constructor; cbn; intros; first [exact I | lia]. Qed.
Lemma ameter_triv_fs_laws : ameter_fs_laws ameter_triv.
Proof. constructor; cbn; intros; exact I. Qed.

(* ---- the closer's contract: copy of fuzz_grant's lib/A/ACfn.v (IdentTop.v:252 converts it to the core's) ------- *)
Section y.
Context {SKi : YI16.sink_head}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
(* fuzz_grant's YE01.v:190, verbatim *)
Definition arodata_okS (segs : list Segment) (B : asyms) (rlo rhi : Z) (rd : reader) : Prop :=
forall a, ((exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (rlo <= a < rhi)) ->
~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO' RHI' : Z.
Local Notation segs := ident_segs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* fuzz_grant's lib/A/ACfn.v:33-72, verbatim but for segs, RLO' / RHI', ajournal's explicit rc SKi and the YE names *)
Definition tfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS segs B RLO' RHI' (aview segs (w_H W) mem) /\
asink_none segs tfib_K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).
Definition tfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
@ajournal rc SKi segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tfib_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO' RHI' : Z) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO' RHI'.
End y.

(* The registered globals of fuzz_identity.asan (sha256 c954b804786cb87f...): the (beg, size) of each of the 50
   descriptors of its asan_globals section (0xa0c60, 64 bytes each), in section order, read with pyelftools. This is the
   concrete list G of the contract (lib/A/Prog/LLVMFuzzerTestOneInput.v); the membership facts the walks take
   (G_HW, G_SW, G_CAT, G_IN, G_OUT, HWFG, G_IMGSTR) are proved from it by computation below, so only GM (the start-up
   certificate that the runtime marks each of them) stays a premise. *)
Definition IDENT_GLOBS : list (Z * Z) :=
[(0x20f80, 2); (0x20fa0, 7); (0x20fc0, 6); (0x20fe0, 36); (0x21040, 7); (0x21060, 7); (0x21080, 8); 
 (0x210a0, 5); (0x210e0, 36); (0x21140, 7); (0x21160, 7); (0x21180, 8); (0x211a0, 5); (0x211c0, 3); 
 (0x211e0, 7); (0x21200, 6); (0x21240, 6); (0x21260, 23); (0x212a0, 6); (0x212c0, 22); (0x21300, 7); 
 (0x21320, 7); (0x21340, 29); (0x21380, 12); (0x213a0, 29); (0x213e0, 6); (0x21400, 23); (0x21440, 8); 
 (0x21460, 6); (0x21480, 24); (0x214c0, 8); (0x214e0, 7); (0x21500, 24); (0x21540, 9); (0x21560, 7); 
 (0x21580, 24); (0x215c0, 9); (0x215e0, 7); (0x21600, 23); (0x21640, 8); (0x21660, 7); (0x21680, 23); 
 (0x216c0, 8); (0x216e0, 7); (0x21700, 24); (0x21740, 8); (0x9b180, 24); (0x9b1c0, 24); (0x9b200, 24); 
 (0x9b240, 3256)].
Lemma globs_In_b : forall a n l, existsb (fun p => (fst p =? a) && (snd p =? n)) l = true -> In (a, n) l.
Proof.
intros a n l H. apply existsb_exists in H as ((x & y) & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
Qed.

(* ---- the link ---------------------------------------------------------------------------------------------- *)
Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation SKA := ident_asan_sink_head.
Local Notation PI := (@PI_ident rc).
Local Notation SEGS := (@pa_segs _ ident_listing PI).
Local Notation VAL := (@pa_val _ ident_listing PI).
Local Notation SIGMA := (@pa_sigma _ ident_listing PI).
Local Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Variable IdentB : asyms.
(* the core's sink names (YE00 / YE01 on the relocated core) *)
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Local Notation ARS := (@arodata_okS).

(* The contract-level side conditions, at the instantiation. *)
Lemma HLIBK_ok : forall pl fs K, @LIBK identity_shape pl fs K = K (LL 0 fs []).
Proof. intros pl fs K. reflexivity. Qed.
Lemma HRO_ok : forall rdr, ARS SEGS IdentB RLO RHI rdr ->
arodata_okP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) IdentB rdr.
Proof. intros rdr H. exact H. Qed.
Lemma HSTK_ok : LLVMFuzzerTestOneInput.STK_LLVMF <= LLVMF_STK.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma HEV_ok : LLVMFuzzerTestOneInput.EV_LLVMF <= EV_LIB.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma HLIVE_ok : LLVMFuzzerTestOneInput.LIVE_LLVMF <= LIVE_LIB.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma HXM_ok : forall n, LLVMFuzzerTestOneInput.EV_LLVMF * (mo_malloc ameter_triv 256 + mo_free ameter_triv) <= XL0 n.
Proof. intros n. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma HMT0_ok : forall s s' : astate, mo_le ameter_triv s s' 0.
Proof. intros s s'. exact I. Qed.
(* RO at the ASan head: every read-only segment of fuzz_identity.asan and the relro range lie below 0x5f8648. *)
Lemma RO_ok : @ro_below_ofl SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) SKA.
Proof.
unfold ro_below_ofl. intros a Ha. cbv [YI16.sk_ofl_head ident_asan_sink_head].
destruct Ha as [(s & Hin & Hw & Hr) | Hr].
- change (In s ident_segs) in Hin. unfold ident_segs, Asan.M.loaded_segments in Hin.
  repeat (destruct Hin as [<- | Hin];
    [first [vm_compute in Hw; discriminate
           | match type of Hr with Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
               let l := eval vm_compute in lo in let l' := eval vm_compute in lo' in let h := eval vm_compute in sz in
               change lo with l in Hr; change lo' with l' in Hr; change sz with h in Hr end; lia] |]);
  contradiction.
- change (0x9ada0 <= a < 0x9d0a8) in Hr. lia.
Qed.
(* The image facts two leaf walks take (closed goals, decided by computation). *)
Lemma TBLSEP_ok : (VAL (A_OBJ 17) + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 17)) /\
(VAL (A_OBJ 17) + 24 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= VAL (A_OBJ 17)).
Proof.
split; first [left; apply Z.leb_le; vm_compute; reflexivity | right; apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma HWFIMG_ok : IMG_LO + 64 <= @reac_box_family_of.FAMOF_HWF rc PI /\ @reac_box_family_of.FAMOF_HWF rc PI + 100 <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma HWFSEP_ok :
(@reac_box_family_of.FAMOF_HWF rc PI + 36 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= @reac_box_family_of.FAMOF_HWF rc PI) /\
(@reac_box_family_of.FAMOF_HWF rc PI + 36 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= @reac_box_family_of.FAMOF_HWF rc PI).
Proof.
split; first [left; apply Z.leb_le; vm_compute; reflexivity | right; apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* The core's runtime contracts (open, by name; the names of LLVMFuzzerTestOneInput.v's Section). *)
Hypothesis LAWS : AR_laws SEGS IdentB.
Hypothesis TL : PALib IdentB.
Hypothesis TLF : PALibF IdentB.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis ML : model_laws (as_universe IdentB).
Hypothesis ASM0 : @astack_malloc_realizes fx rc SEGS IdentB 0.
Hypothesis ASM3 : @astack_malloc_realizes fx rc SEGS IdentB 3.
Hypothesis ASM4 : @astack_malloc_realizes fx rc SEGS IdentB 4.
Hypothesis SMP : stack_malloc_progressP IdentB.
Hypothesis ASF : astack_free_law SEGS IdentB.
Hypothesis FFL : frame_flag_lawP SEGS IdentB.
Hypothesis AMEMSET : @aintrin_realizes fx rc SEGS IdentB OSet (SIGMA IS___asan_memset).
Hypothesis AMEMCPY : @aintrin_realizes fx rc SEGS IdentB OCpy (SIGMA IS___asan_memcpy).
Hypothesis ABCMP : @abcmp_realizes fx rc SEGS IdentB (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : @astrlen_realizes fx rc SEGS IdentB (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : @astrcmp_realizes fx rc SEGS IdentB (SIGMA IS___interceptor_trampoline_strcmp).
Hypothesis ASSF5 : aset_shadow_realizes SEGS IdentB (SIGMA IS___asan_set_shadow_f5) 0xf5.
Local Notation G := IDENT_GLOBS (only parsing).
Hypothesis GM : globs_marked SEGS IdentB G.
Hypothesis IV : img_shadow_vis SEGS IdentB.
Lemma HWFG : In (@reac_box_family_of.FAMOF_HWF rc PI, 36) G.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
@ajournal rc SKA SEGS IdentB STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the callee contracts, each from its proved walk ---------------------------------------------------- *)
Lemma HCHK_ok : @check_str.tcheck_str_spec fx rc SKA PI IdentB.
Proof. exact (@check_str.pb_check_str fx rc SKA PI IdentB LAWS TL ASTRLEN). Qed.
Lemma HCAT_ok : @reac_box_catalogue.tcat_spec fx rc SKA PI IdentB (BASE + AF_reac_box_catalogue)
(@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI).
Proof. exact (@reac_box_catalogue.pb_reac_box_catalogue fx rc SKA PI IdentB LAWS TL). Qed.
Lemma HCATD_ok : @reac_box_catalogue_defect.treac_box_catalogue_defect_spec fx rc SKA PI IdentB G.
Proof. exact (@reac_box_catalogue_defect.pb_reac_box_catalogue_defect fx rc SKA PI IdentB G LAWS TL GM IV ASTRCMP). Qed.
Lemma HSTEM_ok : @reac_box_family_stem.treac_box_family_stem_spec fx rc SKA PI IdentB.
Proof. exact (@reac_box_family_stem.pb_reac_box_family_stem fx rc SKA PI IdentB LAWS TL TBLSEP_ok). Qed.
Lemma HFWS_ok : @reac_identity_fw_str.treac_identity_fw_str_spec fx rc SKA PI IdentB.
Proof. exact (@reac_identity_fw_str.pb_reac_identity_fw_str fx rc SKA PI IdentB LAWS TL). Qed.
Lemma HINIT_ok : @reac_identity_init.treac_identity_init_spec fx rc SKA PI IdentB (BASE + AF_reac_identity_init).
Proof. exact (@reac_identity_init.pb_reac_identity_init fx rc SKA PI IdentB LAWS AMEMSET). Qed.
Lemma HING_ok : @reac_identity_ingest.treac_identity_ingest_spec fx rc SKA PI IdentB.
Proof. exact (@IngestWalk.pb_reac_identity_ingest fx rc SKA PI IdentB LAWS TL). Qed.
Lemma HFAM_ok : @reac_box_family_of.treac_box_family_of_spec fx rc SKA PI IdentB.
Proof.
exact (@reac_box_family_of.pb_reac_box_family_of fx rc SKA PI IdentB LAWS TL ABCMP G IV GM HWFG HWFIMG_ok HWFSEP_ok).
Qed.
Lemma HWU_ok : @write_uint.twrite_uint_spec fx rc SKA PI IdentB.
Proof. exact (@write_uint.pb_write_uint fx rc SKA PI IdentB TL TLF LAWS ML ASM0 SMP ASF FFL). Qed.
Lemma HVS_ok : @reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec fx rc SKA PI IdentB.
Proof. exact (@reac_identity_reac_ver_str.pb_reac_identity_reac_ver_str fx rc SKA PI IdentB LAWS TL PSIG HWU_ok). Qed.
Lemma HSB_ok : @sb_dec.tsb_dec_spec fx rc SKA PI IdentB.
Proof. apply (@sb_decWalk.pb_sb_dec fx rc SKA PI IdentB); assumption. Qed.
Lemma HPD_ok : @put_dec.tput_dec_spec fx rc SKA PI IdentB.
Proof. apply (@put_dec.pb_put_dec fx rc SKA PI IdentB); assumption. Qed.
Lemma HBN_ok : @reac_box_name.treac_box_name_spec fx rc SKA PI IdentB G.
Proof.
exact (@reac_box_name_walk.pb_reac_box_name fx rc SKA PI IdentB G RO_ok TL LAWS ML ASM3 SMP ASF FFL TLF
AMEMSET AMEMCPY ABCMP ASTRLEN ASSF5 GM IV PSIG HSB_ok).
Qed.

(* ---- the entry contract's image facts (LLVMFuzzerTestOneInput.llvmf_img, LLVMFuzzerTestOneInput.v:246-305) --- *)
(* Every byte llvmf_img reads is read-only data of fuzz_identity.asan: .rodata (segment 0x10000, r--) or
   .data.rel.ro inside [pa_relro_lo, pa_relro_hi). arodata_okP gives such a byte as seg_rom when it is not the
   runtime's own and not errno, and each seg_rom byte is then decided by vm_compute of a closed checker over
   ident_segs. What the segments do not decide is open, by name (facts of the core's IdentB and G), except G_IMGSTR:
   - HIMG_UNOWNED: the bytes llvmf_img reads are not in as_owned_static and not errno. It is one fact over the
     intervals IDENT_RO_READS, which the closer checks against the core's owned-static list by one computation
     (cgif lib/A/AD1u.v FINV_IVS_unowned): object 5 (0x10370, 8 bytes) and the body [beg, beg + size) of each
     registered global llvmf_img reads (asan_globals entries 1-15, 17, 19, 22, 24, 26, 29, 32, 35, 38, 41, 44 and
     46-49). It is not stated over all of in_roP: that is false. Object 1 (0x9c3b0, in .got inside
     [pa_relro_lo, pa_relro_hi)) is the GOT cell that holds the shadow offset, which asyms_ok.aso_cover puts in
     as_owned_static (asyms_areas: as_got_shadow). The guard bytes after a global's body are not in
     IDENT_RO_READS either: fuzz_grant's generated owned-static list holds such tails (cgif lib/A/AF0m.v:285).
   - G_IMGSTR, proved below from G by computation: the registered globals (asan_globals entries 4-7, 9-15, 17, 19,
     22, 24, 26, 29, 32, 35, 38, 41, 44: address, size) of the strings llvmf_img reads as image strings (rbn_glob, catd_glob).
   - ZS_STEM, ZS_NAME: in_zs of the two 24-byte switch tables, as llvmf_img and rbn_img state it. *)
(* HIMG's reads are disjoint
   from the core's Tfib_owned_static on both builds,
   but 30 of this build's 31 read ranges end EXACTLY
   at the first owned redzone byte.
   *)
Definition IDENT_RO_READS : list (Z * Z) :=
[(0x10370, 8);     (* object 5: the 8-byte constant 0x03f03f03f03f03f1 (.rodata, no symbol) *)
 (0x20fa0, 7); (0x20fc0, 6);     (* fuzz/fuzz_identity.c's .str.2 " in / ", .str.3 " out)" *)
 (0x20fe0, 36);    (* HW_TABLE *)
 (0x21040, 7); (0x21060, 7); (0x21080, 8); (0x210a0, 5);     (* fuzz_identity.c's .str.4 .. .str.7 *)
 (0x210e0, 36);    (* HW_FAMILY (src/reac_box_facts.c) *)
 (0x21140, 7); (0x21160, 7); (0x21180, 8); (0x211a0, 5); (0x211c0, 3); (0x211e0, 7); (0x21200, 6);
                   (* reac_box_facts.c's .str, .str.1 .. .str.6 *)
 (0x21260, 23); (0x212c0, 22); (0x21340, 29); (0x213a0, 29); (0x21400, 23); (0x21480, 24); (0x21500, 24);
 (0x21580, 24); (0x21600, 23); (0x21680, 23); (0x21700, 24);
                   (* src/reac_ctrlblk.c's .str.23, .25, .28, .30, .32, .35, .38, .41, .44, .47, .50 *)
 (0x9b180, 24); (0x9b1c0, 24); (0x9b200, 24);
                   (* switch.table.LLVMFuzzerTestOneInput, .reac_box_family_stem, .reac_box_name *)
 (0x9b240, 3256)]. (* BOX_CATALOGUE *)
Hypothesis HIMG_UNOWNED : forall x, Exists (in_zr x) IDENT_RO_READS ->
~ Exists (in_zr x) (as_owned_static IdentB) /\ ~ (as_errno IdentB <= x < as_errno IdentB + 4).
Definition HIMG_STRS : list (Z * Z) :=
[(0x21040, 7); (0x21060, 7); (0x21080, 8); (0x210a0, 5); (0x21140, 7); (0x21160, 7); (0x21180, 8); (0x211a0, 5); (0x211c0, 3);
 (0x211e0, 7); (0x21200, 6); (0x21260, 23); (0x212c0, 22); (0x21340, 29); (0x213a0, 29); (0x21400, 23);
 (0x21480, 24); (0x21500, 24); (0x21580, 24); (0x21600, 23); (0x21680, 23); (0x21700, 24)].
Lemma G_IMGSTR : incl HIMG_STRS G.
Proof.
intros (a & n) Hin. apply globs_In_b.
assert (Hall : forallb (fun p => existsb (fun q => (fst q =? fst p) && (snd q =? snd p)) IDENT_GLOBS) HIMG_STRS = true)
  by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) Hall (a, n) Hin).
Qed.
Hypothesis ZS_STEM : in_zs IdentB (VAL (A_OBJ 17)) 24.
Hypothesis ZS_NAME : in_zs IdentB (VAL (A_OBJ 21)) 24.

(* The closed checkers: computed over ident_segs on closed arguments only. *)
Definition himg_in (x : Z) : Prop := Exists (in_zr x) IDENT_RO_READS.
Definition himg_rng_b (a n : Z) : bool :=
existsb (fun iv => (fst iv <=? a) && (a + n <=? fst iv + snd iv)) IDENT_RO_READS.
Definition himg_byte_b (x v : Z) : bool :=
match seg_rom ident_segs (Z_to_bv 64 x) with Some b => bv_unsigned b =? bv_unsigned (Z_to_bv 8 v) | None => false end.
Definition himg_val_b (a : Z) (n : nat) (v : Z) : bool :=
himg_rng_b a (Z.of_nat n) && forallb (fun k => himg_byte_b (a + Z.of_nat k) (YO0f.le_byte v n k)) (seq 0 n).
Definition himg_arr_b (a : Z) (l : list Z) : bool :=
himg_rng_b a (Z.of_nat (length l)) &&
forallb (fun j => himg_byte_b (a + Z.of_nat j + Z.of_nat 0) (YO0f.le_byte (nth j l 0) 1 0) &&
  (0 <=? nth j l 0) && (nth j l 0 <? 256)) (seq 0 (length l)).
Definition himg_tail_b (e : Z) : bool :=
forallb (fun k => match seg_rom ident_segs (Z_to_bv 64 (e + 1 + Z.of_nat k)) with Some _ => true | None => false end)
  (seq 0 (Z.to_nat (7 - e mod 8))).
Definition himg_glob_b (a n : Z) : bool := existsb (fun g => (fst g <=? a) && (a + n <=? fst g + snd g)) HIMG_STRS.
(* rbn_imgstr's closed part *)
Definition himg_str_b (a : Z) (s : list Z) : bool :=
(IMG_LO + 64 <=? a) && (a + Z.of_nat (length s) + 1 + 64 <=? IMG_TOP) &&
forallb (fun c => (0 <? c) && (c <? 256)) s && himg_arr_b a (s ++ [0]) &&
himg_tail_b (a + Z.of_nat (length s)) && himg_glob_b a (Z.of_nat (length s) + 1).
(* catd_rostr's closed part *)
Definition himg_rostr_b (x : Z) (s : list byte) : bool :=
himg_arr_b x (reac_box_catalogue_defect.catd_lz s) && forallb (fun b : byte => negb (bv_unsigned b =? 0)) s &&
himg_glob_b x (Z.of_nat (length s) + 1) &&
(IMG_LO + 64 <=? x) && (x + Z.of_nat (length s) + 1 + 64 <=? IMG_TOP).
(* the catalogue row's fields, read from the image: little-endian value, sign of a 4-byte field, C string *)
Fixpoint himg_le (a : Z) (n : nat) : Z :=
match n with
| O => 0
| S n' => match seg_rom ident_segs (Z_to_bv 64 a) with Some b => bv_unsigned b | None => 0 end + 256 * himg_le (a + 1) n'
end.
Definition himg_s32 (u : Z) : Z := if u <? 2 ^ 31 then u else u - 2 ^ 32.
Fixpoint himg_cstr (a : Z) (fuel : nat) : list byte :=
match fuel with
| O => []
| S f => match seg_rom ident_segs (Z_to_bv 64 a) with
         | Some b => if bv_unsigned b =? 0 then [] else b :: himg_cstr (a + 1) f
         | None => []
         end
end.
Definition himg_cat_P (r : Z) : Z := himg_le (0x9b240 + 296 * r + 8) 8.
Definition himg_cat_I (r : Z) : Z := himg_s32 (himg_le (0x9b240 + 296 * r + 16) 4).
Definition himg_cat_O (r : Z) : Z := himg_s32 (himg_le (0x9b240 + 296 * r + 20) 4).
Definition himg_cat_S (r : Z) : list byte := himg_cstr (himg_cat_P r) 64.
Definition himg_row_b (r : Z) : bool :=
(-2 ^ 31 <=? himg_cat_I r) && (himg_cat_I r <? 2 ^ 31) && (-2 ^ 31 <=? himg_cat_O r) && (himg_cat_O r <? 2 ^ 31) &&
(0 <=? himg_cat_P r) && (himg_cat_P r <? 2 ^ 64) &&
himg_val_b (0x9b240 + 296 * r + 8) 8 (himg_cat_P r) && himg_val_b (0x9b240 + 296 * r + 16) 4 (himg_cat_I r) &&
himg_val_b (0x9b240 + 296 * r + 20) 4 (himg_cat_O r) &&
((himg_cat_P r =? 0) || himg_rostr_b (himg_cat_P r) (himg_cat_S r)).

Lemma himg_rng_ok : forall a n x, himg_rng_b a n = true -> a <= x < a + n -> himg_in x.
Proof.
intros a n x H Hx. unfold himg_rng_b in H. apply existsb_exists in H as ((q & z) & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
apply Exists_exists. exists (q, z). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* every interval of IDENT_RO_READS lies in segment 0x10000 (r--) or in [pa_relro_lo, pa_relro_hi) *)
Lemma himg_ro_seg_b : forallb (fun iv => ((0x10000 <=? fst iv) && (fst iv + snd iv <=? 0x30000)) ||
((0x9ada0 <=? fst iv) && (fst iv + snd iv <=? 0x9d0a8))) IDENT_RO_READS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma himg_in_cases : forall x, himg_in x -> 0x10000 <= x < 0x30000 \/ 0x9ada0 <= x < 0x9d0a8.
Proof.
intros x Hx. apply Exists_exists in Hx as (iv & Hin & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) himg_ro_seg_b iv Hin) as H. cbv beta in H.
apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
Qed.
Lemma himg_byte_ok : forall x v, himg_byte_b x v = true -> seg_rom ident_segs (Z_to_bv 64 x) = Some (Z_to_bv 8 v).
Proof.
intros x v H. unfold himg_byte_b in H.
destruct (seg_rom ident_segs (Z_to_bv 64 x)) as [b|]; [|cbn in H; discriminate H].
f_equal. apply bv_eq. apply Z.eqb_eq. exact H.
Qed.
Lemma himg_tail_ok : forall e, himg_tail_b e = true ->
forall x, e < x < e - e mod 8 + 8 -> seg_rom ident_segs (Z_to_bv 64 x) <> None.
Proof.
intros e H x Hx. unfold himg_tail_b in H. apply forallb_forall with (x := Z.to_nat (x - e - 1)) in H.
- rewrite Z2Nat.id in H by lia. replace (e + 1 + (x - e - 1)) with x in H by lia.
  destruct (seg_rom ident_segs (Z_to_bv 64 x)); [discriminate | cbn in H; discriminate H].
- pose proof (Z.mod_pos_bound e 8 ltac:(lia)). apply in_seq. lia.
Qed.
Lemma himg_in_ro : forall x, himg_in x -> in_roP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) x.
Proof.
intros x Hx. destruct (himg_in_cases x Hx) as [Hs|Hs]; [left | right].
- exists Asan.Asan_segment_000. split; [left; reflexivity|]. split; [reflexivity|].
  change (0x10000 <= x < 0x10000 + 0x20000). lia.
- change (0x9ada0 <= x < 0x9d0a8). exact Hs.
Qed.
Lemma himg_in_img : forall x, himg_in x -> in_img SEGS x.
Proof.
intros x Hx. destruct (himg_in_cases x Hx) as [Hs|Hs].
- exists Asan.Asan_segment_000. split; [left; reflexivity|]. change (0x10000 <= x < 0x10000 + 0x20000). lia.
- exact (ident_relro_img x Hs).
Qed.
Local Notation himg_ro W mem :=
(arodata_okP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) IdentB (aview SEGS (w_H W) mem)).
(* rd W mem reads seg_rom at the program's read-only objects (YCbq.mbyte_of_aview against the empty overlay) *)
Lemma himg_mbyte : forall (W : world SEGS) mem x, himg_ro W mem -> himg_in x ->
mbyte SEGS (mrestrict (w_H W) mem) x = seg_rom SEGS (Z_to_bv 64 x).
Proof.
intros W mem x HR Hx. destruct (HIMG_UNOWNED x Hx) as [Ho He].
exact (mbyte_of_aview SEGS (fun _ => true) (w_H W) mem mem x (HR x (himg_in_ro x Hx) Ho He)).
Qed.
Lemma himg_val : forall (W : world SEGS) mem a n v, himg_ro W mem -> himg_val_b a n v = true ->
YI04.val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v HR H k Hk. unfold himg_val_b in H. apply andb_prop in H as [Hr H].
apply forallb_forall with (x := k) in H; [|apply in_seq; lia].
pose proof (himg_rng_ok a (Z.of_nat n) (a + Z.of_nat k) Hr ltac:(lia)) as Hi.
rewrite (himg_mbyte W mem _ HR Hi). exact (himg_byte_ok _ _ H).
Qed.
Lemma himg_arr : forall (W : world SEGS) mem a l, himg_ro W mem -> himg_arr_b a l = true ->
garr8 SEGS (mrestrict (w_H W) mem) a l.
Proof.
intros W mem a l HR H j Hj. unfold himg_arr_b in H. apply andb_prop in H as [Hr H].
apply forallb_forall with (x := j) in H; [|apply in_seq; lia].
apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
split; [|lia]. intros k Hk. assert (k = 0%nat) as -> by lia.
pose proof (himg_rng_ok a (Z.of_nat (length l)) (a + Z.of_nat j + Z.of_nat 0) Hr ltac:(lia)) as Hi.
rewrite (himg_mbyte W mem _ HR Hi). exact (himg_byte_ok _ _ H).
Qed.
Lemma himg_glob : forall a n, himg_glob_b a n = true -> exists q z, In (q, z) G /\ q <= a /\ a + n <= q + z.
Proof.
intros a n H. unfold himg_glob_b in H. apply existsb_exists in H as ((q & z) & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
exists q, z. split; [exact (G_IMGSTR _ Hin)|]. lia.
Qed.
Lemma himg_str : forall (W : world SEGS) mem a s, himg_ro W mem -> himg_str_b a s = true ->
@reac_box_name.rbn_imgstr rc PI IdentB G W mem a s.
Proof.
intros W mem a s HR H. unfold himg_str_b in H.
apply andb_prop in H as [H Hg]. apply andb_prop in H as [H Ht]. apply andb_prop in H as [H Ha].
apply andb_prop in H as [H Hc]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof Ha as Hr. unfold himg_arr_b in Hr. apply andb_prop in Hr as [Hr _].
pose proof (length_app s [0]) as HL. cbn [length] in HL.
unfold reac_box_name.rbn_imgstr. split; [exact H1|]. split; [exact H2|].
split.
{ apply Forall_forall. intros c Hin. apply forallb_forall with (x := c) in Hc; [|exact Hin].
  apply andb_prop in Hc as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. lia. }
split; [exact (himg_arr W mem _ _ HR Ha)|].
split; [exact (himg_glob _ _ Hg)|].
split.
{ intros x Hx. pose proof (himg_rng_ok a (Z.of_nat (length (s ++ [0]))) x Hr ltac:(lia)) as Hi.
  destruct (HIMG_UNOWNED x Hi) as [Ho He]. split; [exact (himg_in_img x Hi)|]. split; assumption. }
intros x Hx. exact (himg_tail_ok _ Ht x Hx).
Qed.
Lemma himg_rostr : forall (W : world SEGS) mem x s, himg_ro W mem -> himg_rostr_b x s = true ->
@reac_box_catalogue_defect.catd_rostr rc PI G W mem x s.
Proof.
intros W mem x s HR H. unfold himg_rostr_b in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H Hg].
apply andb_prop in H as [Ha Hn]. apply Z.leb_le in H4. apply Z.leb_le in H5.
unfold reac_box_catalogue_defect.catd_rostr. split; [exact (himg_arr W mem _ _ HR Ha)|].
split.
{ intros Hin. apply forallb_forall with (x := Z_to_bv 8 0) in Hn; [|exact Hin]. cbn in Hn. discriminate Hn. }
split; [exact (himg_glob _ _ Hg)|]. split; [exact H4 | exact H5].
Qed.

(* the closed facts, one per read *)
Lemma img_obj5_b : himg_val_b 0x10370 8 0x03f03f03f03f03f1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_hw_b : himg_arr_b 0x20fe0 LLVMFuzzerTestOneInput.HW_ROWS = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_hw16_b : himg_arr_b 0x210e0 LLVMFuzzerTestOneInput.HW_ROWS = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_sw1_b : himg_val_b 0x9b180 8 0x21040 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_sw2_b : himg_val_b (0x9b180 + 8) 8 0x21060 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_sw3_b : himg_val_b (0x9b180 + 16) 8 0x21080 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_swstr1_b : himg_str_b 0x21040 (disco_box_name_model.bn_STEM 1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_swstr2_b : himg_str_b 0x21060 (disco_box_name_model.bn_STEM 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_swstr3_b : himg_str_b 0x21080 (disco_box_name_model.bn_STEM 3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_reac_b : himg_arr_b 0x210a0 (disco_box_name_model.bn_STEM 0 ++ [0]) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_in_b : himg_arr_b 0x20fa0 [32; 105; 110; 32; 47; 32; 0] = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_out_b : himg_arr_b 0x20fc0 [32; 111; 117; 116; 41; 0] = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_stem1_b : himg_val_b 0x9b1c0 8 0x21140 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_stem2_b : himg_val_b (0x9b1c0 + 8) 8 0x21160 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_stem3_b : himg_val_b (0x9b1c0 + 16) 8 0x21180 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nm1_b : himg_val_b 0x9b200 8 0x21140 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nm2_b : himg_val_b (0x9b200 + 8) 8 0x21160 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nm3_b : himg_val_b (0x9b200 + 16) 8 0x21180 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmstr1_b : himg_str_b 0x21140 (disco_box_name_model.bn_STEM 1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmstr2_b : himg_str_b 0x21160 (disco_box_name_model.bn_STEM 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmstr3_b : himg_str_b 0x21180 (disco_box_name_model.bn_STEM 3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmreac_b : himg_str_b 0x211a0 (disco_box_name_model.bn_STEM 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmpo_b : himg_str_b 0x211c0 [32; 40] = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmin_b : himg_str_b 0x211e0 [32; 105; 110; 32; 47; 32] = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmout_b : himg_str_b 0x21200 [32; 111; 117; 116; 41] = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_nmtbl_b : himg_rng_b 0x9b200 24 = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_rows_b : forallb himg_row_b (map Z.of_nat (seq 0 11)) = true. Proof. vm_compute. reflexivity. Qed.

(* the conjuncts of llvmf_img, in its order *)
Lemma img_obj5 : forall (W : world SEGS) mem, himg_ro W mem ->
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 5)) 8 0x03f03f03f03f03f1.
Proof. intros W mem HR. change (VAL (A_OBJ 5)) with 0x10370. exact (himg_val W mem _ _ _ HR img_obj5_b). Qed.
Lemma img_hw : forall (W : world SEGS) mem, himg_ro W mem ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 6)) LLVMFuzzerTestOneInput.HW_ROWS.
Proof. intros W mem HR. change (VAL (A_OBJ 6)) with 0x20fe0. exact (himg_arr W mem _ _ HR img_hw_b). Qed.
Lemma img_hw_rng : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 100 <= IMG_TOP.
Proof. change (VAL (A_OBJ 6)) with 0x20fe0. lia. Qed.
Lemma img_hw16 : forall (W : world SEGS) mem, himg_ro W mem ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 16)) LLVMFuzzerTestOneInput.HW_ROWS.
Proof. intros W mem HR. change (VAL (A_OBJ 16)) with 0x210e0. exact (himg_arr W mem _ _ HR img_hw16_b). Qed.
Lemma img_sw_al : VAL (A_OBJ 7) mod 8 = 0.
Proof. change (VAL (A_OBJ 7)) with 0x9b180. reflexivity. Qed.
Lemma img_sw : forall (W : world SEGS) mem, himg_ro W mem ->
exists s1 s2 s3,
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 7)) 8 s1 /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 7) + 8) 8 s2 /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 7) + 16) 8 s3 /\
@reac_box_name.rbn_imgstr rc PI IdentB G W mem s1 (disco_box_name_model.bn_STEM 1) /\
@reac_box_name.rbn_imgstr rc PI IdentB G W mem s2 (disco_box_name_model.bn_STEM 2) /\
@reac_box_name.rbn_imgstr rc PI IdentB G W mem s3 (disco_box_name_model.bn_STEM 3).
Proof.
intros W mem HR. change (VAL (A_OBJ 7)) with 0x9b180. exists 0x21040, 0x21060, 0x21080.
split; [exact (himg_val W mem _ _ _ HR img_sw1_b)|]. split; [exact (himg_val W mem _ _ _ HR img_sw2_b)|].
split; [exact (himg_val W mem _ _ _ HR img_sw3_b)|]. split; [exact (himg_str W mem _ _ HR img_swstr1_b)|].
split; [exact (himg_str W mem _ _ HR img_swstr2_b)|]. exact (himg_str W mem _ _ HR img_swstr3_b).
Qed.
Lemma img_reac : forall (W : world SEGS) mem, himg_ro W mem ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 8)) (disco_box_name_model.bn_STEM 0 ++ [0]).
Proof. intros W mem HR. change (VAL (A_OBJ 8)) with 0x210a0. exact (himg_arr W mem _ _ HR img_reac_b). Qed.
Lemma img_in : forall (W : world SEGS) mem, himg_ro W mem ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 9)) [32; 105; 110; 32; 47; 32; 0].
Proof. intros W mem HR. change (VAL (A_OBJ 9)) with 0x20fa0. exact (himg_arr W mem _ _ HR img_in_b). Qed.
Lemma img_out : forall (W : world SEGS) mem, himg_ro W mem ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 10)) [32; 111; 117; 116; 41; 0].
Proof. intros W mem HR. change (VAL (A_OBJ 10)) with 0x20fc0. exact (himg_arr W mem _ _ HR img_out_b). Qed.
Lemma img_stem : forall (W : world SEGS) mem, himg_ro W mem ->
exists t1 t2 t3,
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17)) 8 t1 /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17) + 8) 8 t2 /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17) + 16) 8 t3 /\
0 < t1 < 2 ^ 64 /\ 0 < t2 < 2 ^ 64 /\ 0 < t3 < 2 ^ 64.
Proof.
intros W mem HR. change (VAL (A_OBJ 17)) with 0x9b1c0. exists 0x21140, 0x21160, 0x21180.
split; [exact (himg_val W mem _ _ _ HR img_stem1_b)|]. split; [exact (himg_val W mem _ _ _ HR img_stem2_b)|].
split; [exact (himg_val W mem _ _ _ HR img_stem3_b)|]. lia.
Qed.
(* Object 8 (0x210a0, `.str.7` "REAC" of fuzz_identity.c, asan_globals body (0x210a0, 5)) as an image string: the
   contract's object-8 line in rbn_imgstr form. The body is in
   IDENT_RO_READS and HIMG_STRS; its granule tail (0x210a5 .. 0x210a7) is only asked to be in seg_rom, not read. *)
Lemma img_reac_str_b : himg_str_b 0x210a0 (disco_box_name_model.bn_STEM 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_reac_str : forall (W : world SEGS) mem, himg_ro W mem ->
@reac_box_name.rbn_imgstr rc PI IdentB G W mem (VAL (A_OBJ 8)) (disco_box_name_model.bn_STEM 0).
Proof. intros W mem HR. change (VAL (A_OBJ 8)) with 0x210a0. exact (himg_str W mem _ _ HR img_reac_str_b). Qed.
Lemma img_rbn : forall (W : world SEGS) mem, himg_ro W mem -> @reac_box_name.rbn_img rc PI IdentB G W mem.
Proof.
intros W mem HR. unfold reac_box_name.rbn_img.
split; [change (VAL (A_OBJ 21)) with 0x9b200; reflexivity|].
split; [change (VAL (A_OBJ 21)) with 0x9b200; lia|]. split; [change (VAL (A_OBJ 21)) with 0x9b200; lia|].
split; [exact ZS_NAME|].
change (VAL (A_OBJ 21)) with 0x9b200. change (VAL (A_OBJ 18)) with 0x211a0. change (VAL (A_OBJ 22)) with 0x211c0.
change (VAL (A_OBJ 23)) with 0x211e0. change (VAL (A_OBJ 24)) with 0x21200.
split.
{ intros x Hx. pose proof (himg_rng_ok 0x9b200 24 x img_nmtbl_b ltac:(lia)) as Hi.
  destruct (HIMG_UNOWNED x Hi) as [Ho He]. split; [exact (himg_in_img x Hi)|]. split; assumption. }
split.
{ exists 0x21140, 0x21160, 0x21180.
  split; [exact (himg_val W mem _ _ _ HR img_nm1_b)|]. split; [exact (himg_val W mem _ _ _ HR img_nm2_b)|].
  split; [exact (himg_val W mem _ _ _ HR img_nm3_b)|]. split; [exact (himg_str W mem _ _ HR img_nmstr1_b)|].
  split; [exact (himg_str W mem _ _ HR img_nmstr2_b)|]. exact (himg_str W mem _ _ HR img_nmstr3_b). }
split; [exact (himg_str W mem _ _ HR img_nmreac_b)|].
split; [reflexivity|]. split; [exact (himg_str W mem _ _ HR img_nmpo_b)|].
split; [reflexivity|]. split; [exact (himg_str W mem _ _ HR img_nmin_b)|].
split; [reflexivity|]. exact (himg_str W mem _ _ HR img_nmout_b).
Qed.
Lemma img_cat_al : VAL (A_OBJ 27) mod 8 = 0.
Proof. change (VAL (A_OBJ 27)) with 0x9b240. reflexivity. Qed.
(* The catalogue-row clause (LLVMFuzzerTestOneInput.v:296-305), at the given state; the row's four values are
   read from the image bytes (himg_cat_P/I/O/S). *)
Lemma img_cat : forall (W : world SEGS) mem, himg_ro W mem ->
forall r, 0 <= r < reac_box_catalogue.BOX_COUNT ->
IMG_LO <= VAL (A_OBJ 27) + 296 * r + 8 /\ VAL (A_OBJ 27) + 296 * r + 24 <= IMG_TOP /\
(VAL (A_OBJ 27) + 296 * r + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 27) + 296 * r + 8) /\
(VAL (A_OBJ 27) + 296 * r + 24 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= VAL (A_OBJ 27) + 296 * r + 8) /\
exists I O P sP,
-2 ^ 31 <= I < 2 ^ 31 /\ -2 ^ 31 <= O < 2 ^ 31 /\ 0 <= P < 2 ^ 64 /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 27) + 296 * r + 8) 8 P /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 27) + 296 * r + 16) 4 I /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 27) + 296 * r + 20) 4 O /\
(P <> 0 -> @reac_box_catalogue_defect.catd_rostr rc PI G W mem P sP).
Proof.
intros W mem HR r Hr. change reac_box_catalogue.BOX_COUNT with 11 in Hr.
change (VAL (A_OBJ 27)) with 0x9b240. change (VAL (A_OBJ 1)) with 0x9c3b0. change (VAL (A_OBJ 30)) with 0xa4fb8.
assert (H : himg_row_b r = true).
{ apply (proj1 (forallb_forall himg_row_b (map Z.of_nat (seq 0 11))) img_rows_b).
  replace r with (Z.of_nat (Z.to_nat r)) by lia. apply in_map. apply in_seq. lia. }
unfold himg_row_b in H.
apply andb_prop in H as [H Hs]. apply andb_prop in H as [H VO]. apply andb_prop in H as [H VI].
apply andb_prop in H as [H VP]. apply andb_prop in H as [H P2]. apply andb_prop in H as [H P1].
apply andb_prop in H as [H O2]. apply andb_prop in H as [H O1]. apply andb_prop in H as [I1 I2].
apply Z.leb_le in I1. apply Z.ltb_lt in I2. apply Z.leb_le in O1. apply Z.ltb_lt in O2.
apply Z.leb_le in P1. apply Z.ltb_lt in P2.
split; [lia|]. split; [lia|]. split; [left; lia|]. split; [left; lia|].
exists (himg_cat_I r), (himg_cat_O r), (himg_cat_P r), (himg_cat_S r).
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (himg_val W mem _ _ _ HR VP)|]. split; [exact (himg_val W mem _ _ _ HR VI)|].
split; [exact (himg_val W mem _ _ _ HR VO)|].
intros HP. apply orb_prop in Hs as [Hs|Hs]; [apply Z.eqb_eq in Hs; contradiction|].
exact (himg_rostr W mem _ _ HR Hs).
Qed.

(* The entry contract's image facts, at the instantiation: one split per conjunct of llvmf_img. *)
Lemma ident_himg : forall (W : world SEGS) mem,
arodata_okP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) IdentB (aview SEGS (w_H W) mem) ->
@LLVMFuzzerTestOneInput.llvmf_img rc PI IdentB G W mem.
Proof.
intros W mem HR. unfold LLVMFuzzerTestOneInput.llvmf_img.
split; [exact (img_obj5 W mem HR)|].
split; [exact (img_hw W mem HR)|].
split; [exact (proj1 img_hw_rng)|]. split; [exact (proj2 img_hw_rng)|].
split; [exact (img_hw16 W mem HR)|].
split; [exact img_sw_al|].
split; [exact (img_sw W mem HR)|].
(* object 8: garr8 form (frozen) or rbn_imgstr form, whichever the contract states *)
split; [first [exact (img_reac W mem HR) | exact (img_reac_str W mem HR)]|].
split; [exact (img_in W mem HR)|].
split; [exact (img_out W mem HR)|].
split; [exact ZS_STEM|].
split; [exact (img_stem W mem HR)|].
split; [exact (img_rbn W mem HR)|].
split; [exact img_cat_al|].
exact (img_cat W mem HR).
Qed.

(* Contract hypotheses the proved segments take and the callee lemmas did not need (the contract's names and text,
   lib/A/Prog/LLVMFuzzerTestOneInput.v, at the instantiation; the sink head passed by @). *)
Local Notation rdA W mem := (mrestrict (w_H W) mem).
Lemma G_HW : In (VAL (A_OBJ 6), 36) G.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma G_CAT : In (VAL (A_OBJ 27), 3256) G.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma G_SW : In (VAL (A_OBJ 7), 24) G.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma G_IN : In (VAL (A_OBJ 9), 7) G.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma G_OUT : In (VAL (A_OBJ 10), 6) G.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Hypothesis HUMM : forall c, In c (LLVMFuzzerTestOneInput.LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code IdentB)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code IdentB) then [] else [r]) c)) (as_universe IdentB).
Hypothesis HUMF : forall c, In c (LLVMFuzzerTestOneInput.LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code IdentB)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code IdentB) then [] else [r]) c)) (as_universe IdentB).
Hypothesis AMALLOC4 : @amalloc04_rule fx rc SKA SEGS IdentB ameter_triv.
Hypothesis AFREE4 : @afree04_rule fx rc SKA SEGS IdentB ameter_triv.
Hypothesis AMEMCHR : @amemchr_realizes fx rc SEGS IdentB (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_FP_NIL : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
@ajournal rc SKA SEGS IdentB STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
@ajournal rc SKA SEGS IdentB STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Hypothesis ASINK_NONE_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
@ajournal rc SKA SEGS IdentB STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
asink_none SEGS KS (rdA W mem) md -> asink_none SEGS KS (rdA W' mem') md'.
Hypothesis AMETA_INV_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
@ajournal rc SKA SEGS IdentB STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ameta_inv SEGS KS ly (rdA W mem) M -> ameta_inv SEGS KS ly' (rdA W' mem') M.
#[local] Existing Instance RO_ok.

(* Closes a proved segment's premises from this Section: its hypotheses and the discharged lemmas above. *)
Ltac link_close := first [eassumption | exact HLIBK_ok | exact HSTK_ok | exact HEV_ok | exact HLIVE_ok | exact HXM_ok
  | exact HMT0_ok | exact ameter_triv_laws | exact ameter_triv_fs_laws | exact HRO_ok | exact RO_ok | exact ident_himg
  | exact HCHK_ok | exact HCAT_ok | exact HCATD_ok | exact HSTEM_ok | exact HFWS_ok | exact HINIT_ok | exact HING_ok
  | exact HFAM_ok | exact HVS_ok | exact HPD_ok | exact HBN_ok
  | exact G_HW | exact G_CAT | exact G_SW | exact G_IN | exact G_OUT | exact HWFG | exact G_IMGSTR | exact XL0].

(* ---- the segments: the 16 proved ones from their walks (the assembly on the integration tip), and seg_D3 and
       seg_J; each is discharged from its seg_X_holds, so no segment stays open --------------------------- *)
Lemma hB_ok : @LLVMFuzzerTestOneInput_inv.seg_B fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_B.seg_B_holds fx rc SKA PI); link_close. Qed.
Lemma hC_ok : @LLVMFuzzerTestOneInput_inv.seg_C fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_C.seg_C_holds fx rc SKA PI); link_close. Qed.
Lemma hD1_ok : @LLVMFuzzerTestOneInput_inv.seg_D1 fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_D1.seg_D1_holds fx rc SKA PI); link_close. Qed.
Lemma hD2_ok : @LLVMFuzzerTestOneInput_inv.seg_D2 fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_D2.seg_D2_holds fx rc SKA PI); link_close. Qed.
Lemma hD3_ok : @LLVMFuzzerTestOneInput_inv.seg_D3 fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_D3.seg_D3_holds fx rc SKA PI); link_close. Qed.
Lemma hD4_ok : @LLVMFuzzerTestOneInput_inv.seg_D4 fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_D4.seg_D4_holds fx rc SKA PI); link_close. Qed.
Lemma hD5_ok : @LLVMFuzzerTestOneInput_inv.seg_D5 fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_D5.seg_D5_holds fx rc SKA PI); link_close. Qed.
Lemma hD6_ok : @LLVMFuzzerTestOneInput_inv.seg_D6 fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_D6.seg_D6_holds fx rc SKA PI); link_close. Qed.
Lemma hLP_ok : @LLVMFuzzerTestOneInput_inv.seg_loop fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_Loop.seg_loop_holds fx rc SKA PI); link_close. Qed.
Lemma hRX_ok : @LLVMFuzzerTestOneInput_inv.seg_rec_exit fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_Loop.seg_rec_exit_holds fx rc SKA PI); link_close. Qed.
Lemma hE_ok : @LLVMFuzzerTestOneInput_inv.seg_E fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_E.seg_E_holds fx rc SKA PI); link_close. Qed.
Lemma hF_ok : @LLVMFuzzerTestOneInput_inv.seg_F fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_F.seg_F_holds fx rc SKA PI); link_close. Qed.
Lemma hG_ok : @LLVMFuzzerTestOneInput_inv.seg_G fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_G.seg_G_holds fx rc SKA PI); link_close. Qed.
Lemma hH_ok : @LLVMFuzzerTestOneInput_inv.seg_H fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_H.seg_H_holds fx rc SKA PI); link_close. Qed.
Lemma hI_ok : @LLVMFuzzerTestOneInput_inv.seg_I fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_I.seg_I_holds fx rc SKA PI); link_close. Qed.
Lemma hJ_ok : @LLVMFuzzerTestOneInput_inv.seg_J fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_J.seg_J_holds fx rc SKA PI); link_close. Qed.
Lemma hK_ok : @LLVMFuzzerTestOneInput_inv.seg_K fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_K.seg_K_holds fx rc SKA PI); link_close. Qed.
Lemma hL_ok : @LLVMFuzzerTestOneInput_inv.seg_L fx rc SKA PI IdentB ameter_triv XL0 XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof. eapply (@LLVMFuzzerTestOneInput_L.seg_L_holds fx rc SKA PI); link_close. Qed.

Lemma hA_ok : @LLVMFuzzerTestOneInput_inv.seg_A fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS.
Proof.
exact (@LLVMFuzzerTestOneInput_A.seg_A_holds fx rc SKA PI IdentB ameter_triv XL0 RLO RHI RA_LLVMF A_EMPTY LLVMF_STK
EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS
HSTK_ok LAWS TL TLF ML ameter_triv_laws ameter_triv_fs_laws ASM4 SMP FFL HXM_ok AJ_NIL_IO).
Qed.

(* The walk's contract at the instantiation is the closer's contract, text for text. *)
Theorem ident_entry_link_x :
@tfib_lib_contract_x SKA asink_syms_T KS asink_none ameta_inv fx rc identity_shape IdentB ameter_triv XL0 XL0 RLO RHI.
Proof.
exact (@LLVMFuzzerTestOneInput_inv.pb_LLVMFuzzerTestOneInput fx rc SKA PI IdentB ameter_triv XL0 XL0 RLO RHI
identity_shape RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv ARS HLIBK_ok
hA_ok hB_ok hC_ok hD1_ok hD2_ok hD3_ok hD4_ok hD5_ok hD6_ok hLP_ok hRX_ok hE_ok hF_ok hG_ok hH_ok hI_ok hJ_ok hK_ok hL_ok).
Qed.
End L.

(* The closer's lemma ident_lib_all (IdentTop.v:203), given the open names above at every fx and rc. *)
Theorem ident_entry_link :
forall (IdentB : asyms) (asink_syms_T : Type) (KS : asink_syms_T)
(asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop)
(ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop),
(forall fx rc, @tfib_lib_contract_x ident_asan_sink_head asink_syms_T KS asink_none ameta_inv fx rc identity_shape
  IdentB ameter_triv XL0 XL0 RLO RHI) ->
forall rc, @tfib_lib_contract_x_all ident_asan_sink_head asink_syms_T KS asink_none ameta_inv rc identity_shape
  IdentB ameter_triv XL0 XL0 RLO RHI.
Proof. intros IdentB asink_syms_T KS asink_none ameta_inv H rc fx. exact (H fx rc). Qed.
