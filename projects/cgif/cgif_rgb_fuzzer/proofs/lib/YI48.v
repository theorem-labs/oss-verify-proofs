(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g YI3h YI3d
YI4v YI46 YI4g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_LDR (T : Z) : sstate :=
mkSS PC_RS (sr_set sr_atoms 11%bv (SLit T))
[ YQ0b.mkRegion (Some 2%nat) 0 5136 0 0 [mkChunk 16 (CVal 8 (SLit 65537))] ] None
(mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4)] [] []).
Section b.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation AT_RS := (at_RS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_LD := (at_LD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Section c.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis KLD : forall regs1 memc, AT_LD regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_LD) memc (seg_rom src2segs)) mdc) POST.
Theorem RS_stretch : forall regs1 memc, AT_RS regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 memc HAT. pose proof HAT as (HINV & HREGS & Hfmt & Hi & Hha & G11 & G5 & G9 & G20 & G8 & G21 & G22 & HTlt & HMEM).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof HMEM as (Hslots & S16 & S104 & S64 & S80 & S88 & S96 & Hfc & Hobj & Hcg & Himg & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & _ & Hinv & HT & Hch & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E (ss_LDR T) (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom src2segs))).
{ unfold ss_LDR. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G11; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ 65537); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S16.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom src2segs))) in HJ. clearbody E.
assert (ARR : forall ss ms' T', st_ok src2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_LD -> ms_mem ms' = memc ->
T' = getNextPrimePower2 T -> sr_get (ss_regs ss) 18 = SLit T' -> sr_get (ss_regs ss) 11 = SLit T -> sr_get (ss_regs ss) 22 = SLit 1 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 5; 9; 20; 8; 21]%bv = true ->
SR src2segs (mkCfg ms' mdc) POST).
{ intros ss ms' T' HS' Hrv Hpc Hm ET' Q18 Q11 Q22 QK.
pose proof (regs_kept_of_st_ok src2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc, Hm. apply (KLD (ms_regs ms') memc). unfold at_LD.
split; [| rewrite (st_ok_reg _ _ _ _ 18%bv HS'), Q18; cbn [sv_denot]; subst T; rewrite <- ET'; reflexivity].
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|].
split; [rewrite (st_ok_reg _ _ _ _ 11%bv HS'), Q11; reflexivity|].
split; [rewrite (GK 5%bv ltac:(cbv; auto 20)); exact G5|].
split; [rewrite (GK 9%bv ltac:(cbv; auto 20)); exact G9|].
split; [rewrite (GK 20%bv ltac:(cbv; auto 20)); exact G20|].
split; [rewrite (GK 8%bv ltac:(cbv; auto 20)); exact G8|].
split; [rewrite (GK 21%bv ltac:(cbv; auto 20)); exact G21|].
split; [rewrite (st_ok_reg _ _ _ _ 22%bv HS'), Q22; reflexivity|].
split; [exact HTlt | exact HMEM]. }
assert (HT5 : T = 524309 \/ T = 1048583 \/ T = 2097169 \/ T = 4194319 \/ T = 8388617).
{ pose proof Hch as Hch0. cbv [ts_chain In] in Hch0. unfold MAX_TABLE_SIZE in HTlt. clear - Hch0 HTlt. lia. }
destruct HT5 as [ET | [ET | [ET | [ET | ET]]]]; rewrite ET in HS.
all: jrun_to LAWS src2tbl_ok HS HJ PC_LD; [apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil |].
all: assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x) end).
all: apply (ARR _ _ (getNextPrimePower2 T) HS eq_refl eq_refl Em eq_refl); [rewrite ET; vm_compute; reflexivity | rewrite ET; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.
End c.
End b.
End a.
