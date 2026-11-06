(* Shared ground of the walk of check_words_chain on the ASan build of plugin-hostd/fuzz_command.

   The walk runs the verified symbolic executor over the position-abstract listing (lib/A/Prog/CmdList.v) in
   cgif_file_fuzzer's style (its lib/A/AChc.v for a function's shared ground, lib/A/ACh1.v.. for the stages).
   This file holds what every stage of the walk needs: the per-binary record facts as named Section
   hypotheses, the atoms the walk gives the objects it reads, the regions of the symbolic state at the entry,
   and the lemma that seeds the executor from the contract's premises.

   The named record hypotheses (this port's decision of 2026-10-28 21:50Z: the statements will take the record as
   Section hypotheses, and one lemma file will prove these from CmdBSyms / AR_laws / PALib):

     GREC_RA       the bytes of the recorded calls of g_rec are an addressable range
     GREC_NOT_RT   g_rec lies in the image, and no byte of it is one of the runtime's own cells, nor the errno cell
     LIT_RA        the two format literals are addressable ranges whose shadow bytes are readable

   GREC_RA and LIT_RA are stated over an arbitrary state that satisfies AR, because the walk needs them again
   after every call. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_chain_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the two format literals the loop and the tail read, and the lengths of their bytes without the terminator *)
Definition A_FMT_D : Z := 0x218a0.
Definition A_FMT_SPD : Z := 0x21b40.
Definition LEN_FMT_D : Z := 2.
Definition LEN_FMT_SPD : Z := 3.

(* the side-stack frame: class 4, 1024 bytes in the slot, 992 asked for; list at frame + 32, count at
   frame + 944 (the frame description at 0x207ce) *)
Definition CWC_CID : Z := 4.
Definition CWC_REQ : Z := 992.
Definition OFF_LIST : Z := 32.
Definition LEN_LIST : Z := 769.
Definition OFF_COUNT : Z := 944.
Definition LEN_COUNT : Z := 16.

(* the stage boundaries of the walk, as offsets from BASE (the listing's own numbering) *)
Definition CWC_ENTRY : Z := AF_check_words_chain.                 (* 0x88ca0 *)
Definition CWC_ANDI : Z := AF_check_words_chain + 0x40.           (* 0x88ce0, andi sp,sp,-32 *)
Definition CWC_SM : Z := AF_check_words_chain + 0x74.             (* 0x88d14, the side-stack take *)
Definition CWC_AFTER_SM : Z := AF_check_words_chain + 0x78.       (* 0x88d18 *)
Definition CWC_HDR : Z := AF_check_words_chain + 0xa4.            (* 0x88d44, the frame header *)
Definition CWC_FILL_F8 : Z := AF_check_words_chain + 0x104.       (* 0x88da4, the first shadow fill *)
Definition CWC_FILL_00 : Z := AF_check_words_chain + 0x17c.       (* 0x88e1c, the second shadow fill *)
Definition CWC_GUARD : Z := AF_check_words_chain + 0x1a0.         (* 0x88e40, read < 3 *)
Definition CWC_LOOP : Z := AF_check_words_chain + 0x1d4.          (* 0x88e74, the loop head *)
Definition CWC_LOOP_BACK : Z := AF_check_words_chain + 0x230.     (* 0x88ed0, the back edge *)
Definition CWC_TAIL : Z := AF_check_words_chain + 0x234.          (* 0x88ed4 *)
Definition CWC_TEARDOWN : Z := AF_check_words_chain + 0x2cc.      (* 0x88f6c *)
Definition CWC_EPILOGUE : Z := AF_check_words_chain + 0x318.      (* 0x88fb8 *)
Definition CWC_RET : Z := AF_check_words_chain + 0x354.           (* 0x88ff4, ret *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).

(* The atoms the walk gives the values it cannot name from a register: 32 the shadow base, 33 the runtime's
   use-after-return flag cell, 34 and 35 the two argument pointers of the recorded call. Registers are atoms
   0..31, so a0 = 10 is the recorded call, a1 = 11 the word array and a2 = 12 the word count. *)
Definition cwc_extra (B : asyms) (p1 p2 : Z) : list word :=
map (Z_to_bv 64) [SB; as_uar_cell B; p1; p2].

Definition CWC_Bx : sv := SOff 32 0.
Definition CWC_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* the stack of this call: its own 192 bytes and at most 16 more that the realignment to 32 takes *)
Definition cwc_stack (d : Z) : YP09.region := YP09.mkRegion (Some 2%nat) d 0 d 0 [].

(* the recorded call: the three fields the function reads, all inside g_rec, none of them written here *)
Definition cwc_grec : YP09.region :=
YP09.mkRegion (Some 10%nat) CALL_OFF_NARGS CALL_SIZE 0 0
[YP09.mkChunk CALL_OFF_NARGS (CVal 4 (SLit 3));
YP09.mkChunk (CALL_OFF_ARGS + 8) (CVal 8 (SOff 34 0));
YP09.mkChunk (CALL_OFF_ARGS + 16) (CVal 8 (SOff 35 0))].

Definition cwc_regions (d : Z) : smem :=
[cwc_stack d; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33; cwc_grec].

(* the one shadow entry the executor may lean on at the entry: the recorded call's own bytes. The words of the
   harness and the frame's own bytes are not in it; the stages that read them discharge the obligation from the
   premise that names the block (the words) or from the take of the frame (the frame). *)
Definition cwc_SH : list shent := [mkSHE 10%nat CALL_OFF_NARGS CALL_SIZE].

Definition cwc_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, HPTR 0); (32%nat, mkAF SB SB 0); (33%nat, HPTR 2)] [] [].

Definition ss_cwc (pc : Z) (sregs : list sv) (d : Z) : sstate :=
mkSS pc sregs (cwc_regions d) None cwc_facts.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.

(* --- the per-binary record facts, as named Section hypotheses (this port's decision, 2026-10-28 21:50Z) --- *)

(* GREC_RA: every byte of the recorded calls of g_rec is marked usable, so an instrumented check on a field of
   a recorded call does not reach the error path. *)
Hypothesis GREC_RA : forall ly S W mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS).

(* GREC_NOT_RT: g_rec is an object of the image (in one of its segments), apart from every cell of the runtime's
   record and from the errno cell. With it the journal's "image bytes are kept" part, and the same part of a
   runtime call's kept facts (acall_kept), apply to g_rec, so the fields of the recorded call survive the calls
   the function makes before it reads them. *)
Hypothesis GREC_NOT_RT : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

(* LIT_RA: the bytes of the two format literals are marked usable and their shadow bytes are readable, which is
   what the snprintf wrapper asks of a pointer argument (aread_ok). *)
Hypothesis LIT_RA : forall ly S W mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_FMT_D (LEN_FMT_D + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) A_FMT_D (LEN_FMT_D + 1) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_FMT_SPD (LEN_FMT_SPD + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) A_FMT_SPD (LEN_FMT_SPD + 1).

(* --- what the hypotheses give the walk --- *)

(* rt_rom_view (lib/A/Rt/RtDefs.v), which every wrapper contract asks for, is the contract's arodata premise
   read at the bytes of the image's read-only segments *)
Lemma cwc_rom_view : forall (W : world SEGS) mem,
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> rt_rom_view SEGS B W mem.
Proof.
intros W mem HR a Ha Ho He. apply (HR a); [left; exact Ha | exact Ho | exact He].
Qed.

Lemma cwc_grec_ra_at : forall ly S W mem md lo n,
AR SEGS B ly S W mem md -> A_G_REC + OFF_CALLS <= lo -> lo + n <= A_G_REC + REC_SIZE -> 0 <= n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF lo n.
Proof.
intros ly S W mem md lo n HAR Hlo Hhi Hn x Hx.
apply (GREC_RA ly S W mem md HAR). unfold REC_SIZE, OFF_CALLS in *. lia.
Qed.

(* the errno cell and the runtime's cells are apart from the recorded call, so the journal keeps g_rec *)
Lemma cwc_grec_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
A_G_REC <= a < A_G_REC + REC_SIZE -> fp_spares FP a ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a HJ Ha Hsp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (GREC_NOT_RT a Ha) as (Himg & Ho & He). exact (F3 a Himg Ho He Hsp).
Qed.

(* and so does a runtime call, whose kept facts carry the same image clause *)
Lemma cwc_grec_call_kept : forall lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) a,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er -> A_G_REC <= a < A_G_REC + REC_SIZE ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Er a (_ & _ & K3 & _) Ha.
destruct (GREC_NOT_RT a Ha) as (Himg & Ho & He). exact (K3 a Himg Ho He).
Qed.

(* the runtime's own cells lie outside g_rec, so the symbolic state may hold both as separate regions *)
Lemma cwc_uar_apart : as_uar_cell B + 4 <= A_G_REC \/ A_G_REC + REC_SIZE <= as_uar_cell B.
Proof.
destruct (Z.le_gt_cases (as_uar_cell B + 4) A_G_REC) as [H|H1]; [left; exact H|].
destruct (Z.le_gt_cases (A_G_REC + REC_SIZE) (as_uar_cell B)) as [H|H2]; [right; exact H|].
exfalso. set (a := Z.max (as_uar_cell B) A_G_REC).
assert (Ha : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold a; unfold REC_SIZE in *; lia).
assert (Hu : as_uar_cell B <= a < as_uar_cell B + 4) by (unfold a; unfold REC_SIZE in *; lia).
destruct (GREC_NOT_RT a Ha) as (_ & Ho & _). apply Ho.
pose proof (aso_cover B BOK) as Hc.
assert (Hin : In (as_uar_cell B, 4) (asyms_areas B)) by (unfold asyms_areas; cbn [In]; tauto).
rewrite Forall_forall in Hc. pose proof (Hc _ Hin) as Hex.
rewrite Exists_exists in Hex |- *. destruct Hex as (r & Hr & Hsub).
exists r. split; [exact Hr|]. unfold zr_sub in Hsub. unfold in_zr. cbn [fst snd] in Hsub |- *. lia.
Qed.

Lemma cwc_val_mem_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (aview SEGS (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb.
destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

(* The seed of the walk at the entry: the contract's premises give the symbolic state the executor starts from.
   Shape after cgif_file_fuzzer's lib/A/AChc.v:249-341 (cl_seed_entry). *)
Lemma cwc_seed_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md (cp p1 p2 : Z),
AR SEGS B ly S W mem md ->
astk_ok CHECK_WORDS_CHAIN_STK ly (spZ regs) ->
(forall a, spZ regs - CHECK_WORDS_CHAIN_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
cmd_val_objs ->
getr regs 10 = w64 cp ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (aview SEGS (w_H W) mem) (cp + CALL_OFF_NARGS) 4 3 ->
aval_mem (aview SEGS (w_H W) mem) (cp + CALL_OFF_ARGS + 8) 8 p1 -> 0 <= p1 < 2 ^ 64 ->
aval_mem (aview SEGS (w_H W) mem) (cp + CALL_OFF_ARGS + 16) 8 p2 -> 0 <= p2 < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cwc_extra B p1 p2))) (ss_cwc CWC_ENTRY sr_atoms (-208))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CWC_ENTRY)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CWC_Bx cwc_SH (Eimg (Ereg regs (cwc_extra B p1 p2))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md cp p1 p2 HAR Hstk Hpres HOBJ H10 Hlo Hhi Vn V1 R1 V2 R2.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : CHECK_WORDS_CHAIN_STK = 12496) by reflexivity.
pose proof (pa_val_range (A_OBJ 0)) as Rg0. pose proof (pa_val_range (A_OBJ 1)) as Rg1.
pose proof (pa_val_range (A_OBJ 12)) as Rg12.
pose proof (pa_obj_img 0 ltac:(lia)) as Img0. pose proof (pa_obj_img 1 ltac:(lia)) as Img1.
pose proof (pa_obj_img 12 ltac:(lia)) as Img12.
assert (Ob0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (HOBJ 0%nat ltac:(cbv; lia)); reflexivity).
assert (Ob1 : VAL (A_OBJ 1) = 0xa6448) by (rewrite (HOBJ 1%nat ltac:(cbv; lia)); reflexivity).
assert (Ob12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (HOBJ 12%nat ltac:(cbv; lia)); reflexivity).
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Hual.
pose proof cwc_uar_apart as Hua.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_cell B TL) in Kcell. rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot.
rewrite (palf_got_uar B TLF) in Kgotu.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cwc_extra B p1 p2))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (cwc_extra B p1 p2) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth cwc_extra map] in E32, E33, E34, E35.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 cp) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E10u : bv_unsigned (ew E 10) = cp)
by (rewrite E10; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
split.
- unfold ss_cwc, cwc_regions. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cwc_stack, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, cwc_grec.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CWC_Bx SB);
[unfold CWC_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
rewrite Z.add_0_r. rewrite <- SB_SHADOW_OFF in Kcell. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgotu).
* cbn [base_val]. rewrite E33u. split; [lia|]. split; [lia|].
split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
[reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar).
* cbn [base_val]. rewrite E10u.
unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, A_G_REC, OFF_CALLS, REC_SIZE in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ cp 4 4 (SLit 3) 3);
[reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
exact (cwc_val_mem_of_aval W mem _ _ _ Vn).
-- apply (chunk_ok_val SEGS E _ cp 16 8 (SOff 34 0) p1);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
replace (cp + 16) with (cp + 8 + 8) by lia. exact (cwc_val_mem_of_aval W mem _ _ _ V1).
-- apply (chunk_ok_val SEGS E _ cp 24 8 (SOff 35 0) p2);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
replace (cp + 24) with (cp + 8 + 16) by lia. exact (cwc_val_mem_of_aval W mem _ _ _ V2).
+ apply pairwise_disjoint_of_extents.
unfold cwc_stack, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, cwc_grec, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia.
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
cbn [base_val]. rewrite E2, E10u, E33u.
unfold CALL_OFF_NARGS, CALL_SIZE, A_G_REC, OFF_CALLS, REC_SIZE in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite Ob0, Ob1, Ob12.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite Ob0, Ob1, Ob12 in Hsep.
revert Hslo Hshi H47 Hceil Hstk0 C1 HTS Hlo Hhi Huar Hua Hsep. clear. intros.
repeat match goal with H : _ /\ _ |- _ => destruct H end;
repeat match goal with H : _ \/ _ |- _ => destruct H end;
repeat split; lia.
+ unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in Hlo, Hhi.
unfold facts_ok, cwc_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
repeat apply conj; try exact I; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2];
rewrite ?E2, ?E10u, ?E32u, ?E33u;
change (2 ^ 4) with 16; change (2 ^ 2) with 4; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
unfold SB in *;
try exact Hsp0al; try exact Hual; try lia.
- unfold sh_ok, cwc_SH. constructor; [|constructor]. split.
+ unfold CWC_Bx. cbn [she_m she_lo she_hi].
rewrite (U_atom E 32 SB E32 ltac:(unfold SB; lia)).
rewrite (U_atom E 10 cp E10 ltac:(unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia)).
rewrite SB_SHADOW_OFF.
intros x Hx.
refine (cwc_grec_ra_at ly S W mem md (cp + CALL_OFF_NARGS) (CALL_SIZE - CALL_OFF_NARGS) HAR _ _ _ x Hx);
unfold CALL_OFF_NARGS, CALL_SIZE in *; lia.
+ unfold app_apart, CWC_Bx. cbn [she_m she_lo she_hi].
rewrite (U_atom E 32 SB E32 ltac:(unfold SB; lia)).
rewrite (U_atom E 10 cp E10 ltac:(unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia)).
intros a Ha. unfold SB, CALL_OFF_NARGS, CALL_SIZE, A_G_REC, OFF_CALLS, REC_SIZE in *.
cbn [Z.min Z.max] in Ha. lia.
Qed.

End e.
End c.
End b.
