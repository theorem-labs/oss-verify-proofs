(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported entry-usage lemmas to the new launch model: added launch/rseq hypotheses, string-block offset lemmas (g_str0_top, g_chead, gval_str0), replaced gval_p0 and wsb_eqG, threaded r through drv_chk/stk_chk, counted the model's reserved regions (n_resx) in the GAP bound, restated the entry checks' parts as g_dparts, g_sparts and g_cparts, and decoded encoded statements; the launch input takes its SIGPIPE disposition as a variable sdf; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0UsageEntryK.v, 179 lines within its lines 13-511. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0DefsK Ja0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
Ja0HandoffK Ja0ArtCellsK Ja0DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanCoreK.APCK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0UsageEntryK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBridgeK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvEntryK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0HandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0UsageEntryK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0UsageEntryK.EntryG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["2ex"; "2not"; "3add"; "4nth"; "5Z"; "0E"; "0EXTRA"; "0FULL"; "6word_to_le_bytes"; "7entry_stack_image"; "8build_stack_bytes"; "0R"; "9mrestrict"; ":argH0"; ";e_sp0"; ";kn"]; ["<uE"; "=EVar"; "=edenot"; "=expr"; ">cat_argv_ptr"; "?VZ"; "?Wsb"; "?kfind_word"; "@ahid"; "AAPH0"; "AASEGS0"; "BDRV_REGS"; "BKE_ENVP"; "BKE_P0"; "BKE_SPK"; "Cas0_A0"]; ["EDRV_REGVG"; "Dtid_chk"; "Fgetr"; "Frdn"; "Fwrap_mem"; "GIn"; "Hadd"; "Hle"; "Hlt"; "Hmodulo"; "Hmul"; "Hof_nat"; "Hpow"; "Hsub"; "0argv"; "0cs"]; ["0e"; "0envp"; "0hw"; "0i"; "0model"; "0off"; "0r"; "0rdraw"; "0sp"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0tid"; "0top"; "0uid"; "0v"]; ["0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition tid_chk (cs : acs) : bool :=
match kfind_word (kn cs) (ELit 0) 0x66ecd8 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end.
Section EntryG.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Variable mbase : word.
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abrt : bool.
Variable ur : InputStream.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdf : bool.
Variable apc : N.
Variable r : Z.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
(AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
Hypothesis Hvl : valid_launch
(AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Abbreviation usp := (bv_unsigned sp).
#[local] Abbreviation argc := (Z.of_nat (length argv)).
#[local] Abbreviation envc := (Z.of_nat (length envp)).
#[local] Abbreviation L0 := (Z.of_nat (length (nth 0 argv []))).
#[local] Abbreviation INP := (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Abbreviation entryw := (Z_to_bv 64 (Z.of_N apc)).
#[local] Abbreviation rseq := (kb_rseq (in_kernel INP)).
#[local] Abbreviation top := (ed_top rdraw).
#[local] Abbreviation utop := (bv_unsigned top).
#[local] Abbreviation LSTR := (Z.of_nat (launch_string_bytes argv envp execfn)).
#[local] Abbreviation STR0 := (usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)).
Hypothesis HRZ : r = rseq_z rseq.
#[local] Abbreviation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
#[local] Abbreviation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Abbreviation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Let AH := argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva.
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Variable cs : acs.
Hypothesis CHK0 : as0_chk cs = true.
Hypothesis CHKD : drv_chk r cs = true.
Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
#[local] Abbreviation A0 := (as0_A0 EXTRA cs E).
#[local] Abbreviation Hx := (ahid A0 model).
#[local] Abbreviation MV := (mrestrict Hx FULL).
#[local] Abbreviation SIMGx := (entry_stack_image INP mbase APH0 entryw sp rdraw).
Ltac LINEQ e Hn H :=
pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
unfold LZ in H;
match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
rewrite ?Z.add_0_r in H.
(* [Ja0DrvEntryK.drv_chk_parts] at this launch, restated by statement so that
   nothing below depends on that lemma's discharged arity (its first explicit
   argument is not [r]); the device of jsoncons/fuzz_json_cursor's
   [Pm8UsageEntryK.g_dparts]. *)
Local Ltac sec := first [ eassumption | exact asan0_in_hull | exact asan0_hull_ok ].
Lemma g_dparts :
pc cs = 0xa71ac
/\ (forall rg e, In (rg, e) DRV_REGS -> sr_get (s_regs (a_ss cs)) (Z_to_bv 5 rg) = e)
/\ lin_nowrapR (kn cs) e_sp0 = true /\ lin_nowrapR (kn cs) (KE_SPK (-48)) = true /\ lin_nowrapR (kn cs) (KE_SPK 8) = true
/\ lin_nowrapR (kn cs) KE_ENVP = true /\ lin_nowrapR (kn cs) (e_str0 r) = true /\ lin_nowrapR (kn cs) (e_str1 r) = true
/\ kfind_word (kn cs) e_sp0 0 8 = Some (EVar V_ARGC) /\ kfind_word (kn cs) e_sp0 8 8 = Some (e_str0 r)
/\ kfind_word (kn cs) e_sp0 16 8 = Some (e_argv1w r)
/\ kfind_wr (kn cs) e_sp0 (-stack_window_depth) = Some (ELit stack_window_depth)
/\ (exists v, kfind_word (kn cs) (ELit 0) 0x68edc0 8 = Some v /\ kfind_word (kn cs) (ELit 0) 0x66ed70 8 = Some v)
/\ (forall lo hi, In (lo, hi) DRV_IMG -> img_cover (kn cs) lo hi = true)
/\ a_fd cs = FdStd.
Proof. eapply drv_chk_parts; sec. Qed.
Lemma g_vals : VZ E 1 = argc /\ VZ E 2 = envc /\ VZ E 3 = L0 /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
Proof. eapply (ent_vals sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_w : VZ E 4 = Z.of_nat (block_pad_len rseq sp top argv envp execfn).
Proof. eapply (ent_w sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_g : VZ E 11 = Z.of_nat (block_items argv envp mod 2).
Proof. eapply (ent_g sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_sp0 : uE E e_sp0 = usp.
Proof. eapply (sp0_val sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.
Lemma g_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256 /\ 0 <= L0 <= 131071.
Proof.
pose proof Hve as [Hle _]. pose proof Hva as (Hac & _ & Hfa & _).
split; [exact Hac|]. split; [lia|]. split; [lia|].
destruct argv as [|a l]; [cbn in Hac; lia|]. inversion Hfa as [|x l' Hx _]; subst. cbn [nth]. exact Hx.
Qed.
Lemma g_vis_high : forall x : word, usp - 8388608 <= bv_unsigned x -> Hx x = false.
Proof. eapply (vis_high sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_simg_top : usp + Z.of_nat (length SIMGx) <= 2 ^ 47
/\ Z.of_nat (length SIMGx) = utop - usp
/\ (usp + Z.of_nat (length SIMGx)) mod 4096 = 0.
Proof.
pose proof (length_entry_stack_image_launch Sv48 INP mbase APH0 entryw sp brk0 rdraw Hlau) as SL.
pose proof (entry_page_top_within_window Sv48 INP mbase sp brk0 rdraw Hlau) as HT.
unfold entry_page_top, va_stack_top, sp_window_hi in HT.
destruct Hlau as ((Hm & _ & _) & _ & _). unfold page_size in Hm.
split; [lia|]. split; [lia|]. replace (usp + Z.of_nat (length SIMGx)) with utop by lia. exact Hm.
Qed.
Lemma g_str0_top : STR0 + LSTR + 8 = utop.
Proof.
pose proof (length_entry_stack_image_launch Sv48 INP mbase APH0 entryw sp brk0 rdraw Hlau) as SL.
assert (SS : Z.of_nat (length SIMGx) = Z.of_nat (cat_string_off rseq sp top argv envp execfn) + LSTR + 8).
{ rewrite entry_stack_image_block, length_build_stack_bytes. unfold cat_string_off.
change (la_rseq (launch_auxv INP sp mbase)) with (kb_rseq (in_kernel INP)).
change (in_argv INP) with argv. change (in_envp INP) with envp. change (in_execfn INP) with execfn. lia. }
lia.
Qed.
Lemma g_str0_ge : usp <= STR0.
Proof. pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)). lia. Qed.
Lemma g_utop_hi : utop <= 2 ^ 47.
Proof.
pose proof (entry_page_top_within_window Sv48 INP mbase sp brk0 rdraw Hlau) as HT.
unfold entry_page_top, va_stack_top in HT. exact HT.
Qed.
Lemma g_gap : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1.
Proof. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.
Lemma g_chead : Z.of_nat (block_head_size rseq argv envp)
= 8 * argc + 8 * envc + 8 * Z.of_nat (block_items argv envp mod 2) + 472 + 32 * rseq_z rseq.
Proof.
unfold block_head_size, block_items, auxv_size, auxv_count, rseq_z.
destruct rseq; cbn [Nat.add]; rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul; cbn [Z.of_nat]; lia.
Qed.
Lemma gval_spk48 : edenot E (KE_SPK (-48)) = Z_to_bv 64 (usp - 48).
Proof.
destruct g_dparts as (_ & _ & _ & L2 & _). destruct g_vals as (_ & _ & _ & U0). pose proof g_rng.
apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK (-48)))) as x eqn:Ex. LINEQ (KE_SPK (-48)) L2 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_spk8 : edenot E (KE_SPK 8) = Z_to_bv 64 (usp + 8).
Proof.
destruct g_dparts as (_ & _ & _ & _ & L3 & _). destruct g_vals as (_ & _ & _ & U0).
apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK 8))) as x eqn:Ex. LINEQ (KE_SPK 8) L3 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_envp : edenot E KE_ENVP = Z_to_bv 64 (usp + 16 + 8 * argc).
Proof.
destruct g_dparts as (_ & _ & _ & _ & _ & L4 & _). destruct g_vals as (U1 & _ & _ & U0).
apply word_of_u. remember (bv_unsigned (edenot E KE_ENVP)) as x eqn:Ex. LINEQ KE_ENVP L4 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_str0 : edenot E (e_str0 r) = Z_to_bv 64 STR0.
Proof.
destruct g_dparts as (_ & _ & _ & _ & _ & _ & L5 & _).
destruct g_vals as (U1 & U2 & _ & U0). pose proof g_w as UW. pose proof g_g as UG.
pose proof g_chead as CH. pose proof g_gap as GR. pose proof g_rng. pose proof g_bounds.
pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
assert (CS : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
= Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
by (unfold cat_string_off; lia).
assert (R01 : r = 0 \/ r = 1) by (rewrite HRZ; unfold rseq_z; destruct (kb_rseq (in_kernel INP)); auto).
pose proof HRZ as HZ. apply word_of_u.
destruct R01 as [Er|Er]; rewrite Er in L5, HZ |- *;
match goal with |- bv_unsigned (edenot E ?e) = _ =>
remember (bv_unsigned (edenot E e)) as x eqn:Ex; LINEQ e L5 HL5; rewrite <- Ex in HL5 end;
lia.
Qed.
Lemma gval_argc : edenot E (EVar V_ARGC) = Z_to_bv 64 argc.
Proof. destruct g_vals as (U1 & _). apply word_of_u. exact U1. Qed.
Definition DRV_REGVG : list (Z * Z) :=
[(1, 0x11315c); (2, usp - 48); (3, 0x10800); (4, 0x66ed80); (8, usp + 8); (9, argc); (10, argc); (11, usp + 8);
(12, usp + 16 + 8 * argc); (18, 0xa71ac); (19, usp + 16 + 8 * argc); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].
Lemma g_reg : forall rg e, In (rg, e) DRV_REGS -> getr R (Z_to_bv 5 rg) = edenot E e.
Proof. eapply (ent_reg sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Theorem entg_regs : forall rg v, In (rg, v) DRV_REGVG -> getr R (Z_to_bv 5 rg) = Z_to_bv 64 v.
Proof.
intros rg v.
intros Hin.
unfold DRV_REGVG in Hin.
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 1 (ELit 0x11315c)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk48|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 4 (ELit 0x66ed80)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 12 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 18 (ELit 0xa71ac)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 19 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 20 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 21 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 22 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 23 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 24 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 25 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 26 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 27 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin.
Qed.
Lemma g_stkword : forall off v, kfind_word (kn cs) e_sp0 off 8 = Some v ->
rdn ASEGS0 MV (Z_to_bv 64 (usp + off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof. eapply (ent_stkword sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Theorem entg_stack_words :
rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 argc))
/\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 STR0)).
Proof.
destruct g_dparts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & _).
pose proof (g_stkword 0 _ K0) as H0. pose proof (g_stkword 8 _ K8) as H8.
rewrite Z.add_0_r, gval_argc in H0. rewrite gval_str0 in H8. auto.
Qed.
Theorem entg_strblock : forall x : word,
STR0 <= bv_unsigned x < utop -> MV x = wrap_mem INP mbase APH0 entryw sp rdraw x.
Proof. eapply (ent_strblock sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Theorem entg_str0 :
rdn ASEGS0 MV (cat_argv_ptr top argv envp execfn 0) (length (nth 0 argv []) + 1) = Some (nth 0 argv [] ++ [Z_to_bv 8 0])
/\ bv_unsigned (cat_argv_ptr top argv envp execfn 0) = STR0.
Proof.
pose proof g_rng as SR. pose proof g_bounds as GB. pose proof g_str0_ge. pose proof g_str0_top. pose proof g_utop_hi.
destruct g_simg_top as (T1 & T2 & _).
assert (Hk' : (0 < length argv)%nat) by lia.
pose proof (bsb_len_lower INP mbase APH0 entryw sp rdraw) as Hlow.
change (in_argv INP) with argv in Hlow. change (in_envp INP) with envp in Hlow. change (in_execfn INP) with execfn in Hlow.
pose proof (entry_stack_image_no_wrap Sv48 INP mbase APH0 entryw sp brk0 rdraw Hlau) as Hnw.
pose proof (total_arg_bytes_firstn_within argv 0%nat Hk') as Hw.
assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity.
assert (PTR : cat_argv_ptr top argv envp execfn 0
= (sp + nat_to_word (cat_string_off rseq sp top argv envp execfn + total_arg_bytes_nat (firstn 0 argv)))%bv).
{ pose proof (cat_string_base_offset Sv48 INP mbase sp brk0 rdraw Hlau) as HB.
change (in_argv INP) with argv in HB. change (in_envp INP) with envp in HB. change (in_execfn INP) with execfn in HB.
rewrite (cat_argv_ptr_offset top argv envp execfn 0%nat Hk'), HB.
rewrite nat_to_word_add_merge. reflexivity. }
assert (UPTR : bv_unsigned (cat_argv_ptr top argv envp execfn 0) = STR0).
{ rewrite PTR, word_add_nat_Z2bv, T0. rewrite u64_lit by lia. lia. }
split; [|exact UPTR].
pose proof (read_argv_cstr_k Sv48 ASEGS0 INP mbase APH0 entryw sp brk0 rdraw 0%nat Hlau Hk') as RA.
change (in_argv INP) with argv in RA. change (in_envp INP) with envp in RA. change (in_execfn INP) with execfn in RA.
rewrite <- RA.
rewrite <- (rdn_wmem_stack ASEGS0 INP mbase APH0 entryw sp rdraw) by lia.
apply rdn_ext; [lia|]. intros x Hxr. unfold wmem. apply entg_strblock.
rewrite UPTR in Hxr. lia.
Qed.
Theorem entg_str0_hi : bv_unsigned (cat_argv_ptr top argv envp execfn 0) + L0 + 1 + 9 <= 2 ^ 47.
Proof.
pose proof g_rng as SR. pose proof g_bounds as GB. pose proof g_str0_top. pose proof g_str0_ge. pose proof g_utop_hi.
destruct entg_str0 as (_ & Hu).
destruct Hvl as [Hfn _].
change (in_execfn INP) with execfn in Hfn.
assert (Hfnlen : 1 <= Z.of_nat (length execfn)).
{ destruct Hfn as [[Hp _]|[(ds & Hds & _)|(ds & rest & Hds & _)]];
[lia | rewrite Hds, length_app; cbn [length dev_fd_prefix]; lia | rewrite Hds, !length_app; cbn [length dev_fd_prefix]; lia]. }
assert (HL : L0 + 1 + Z.of_nat (length execfn) + 1 <= LSTR).
{ unfold launch_string_bytes.
pose proof (Zle_0_nat (length (flatten_strings envp))).
destruct argv as [|a t]; [cbn in GB; lia|]. cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia. }
rewrite Hu.
lia.
Qed.
Lemma g_argH_defined : forall x : word, usp <= bv_unsigned x < usp + Z.of_nat (length SIMGx) -> argH E x = true -> FULL x <> None.
Proof. eapply (argH_defined sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Hypothesis CHKS : stk_chk r cs = true.
(* [Ja0DrvEntryK.stk_chk_parts] / [stk_cover_parts] at this launch, restated
   by statement as [g_dparts] is. *)
Lemma g_sparts :
(forall off, In off (AUX_OFFS r) -> exists v, kfind_word (kn cs) KE_AUX off 8 = Some v)
/\ lin_nowrapR (kn cs) KE_AUX = true /\ lin_nowrapR (kn cs) (e_atrandom r) = true
/\ exists i, kfind_blob16 (kn cs) (KE_RND r) (KE_RNDOFF r) = Some i.
Proof. eapply stk_chk_parts; sec. Qed.
Lemma g_cparts :
lin_nowrapR (kn cs) (KE_RND r) = true /\ lin_nowrapR (kn cs) (escale 8 (EVar V_G)) = true
/\ In (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ r))) (kn cs)
/\ In (KUnk (SA (fst e_auxb) (snd e_auxb + AUXSZ r)) (escale 8 (EVar V_G))) (kn cs)
/\ In (KUnk (SA (KE_RND r) (KE_RNDOFF r + 16)) (EVar V_W)) (kn cs).
Proof. eapply stk_cover_parts; sec. Qed.
Theorem entg_stack_defined : forall i, 0 <= i < Z.of_nat (length SIMGx) -> FULL (Z_to_bv 64 (usp + i)) <> None.
Proof.
intros i.
intros Hi.
pose proof g_rng as SR. pose proof g_bounds as GB. pose proof g_str0_ge. pose proof g_str0_top. pose proof g_utop_hi.
destruct g_simg_top as (T1 & T2 & _).
destruct g_sparts as (CA & LA & LR & (bi & CB)).
destruct g_dparts as (_ & _ & L1 & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
destruct g_vals as (V1 & V2 & _ & V0).
assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).
assert (KW : forall b off v d, kfind_word (kn cs) b off 8 = Some v -> lin_nowrapR (kn cs) b = true ->
(flat E (SA b off) 8 -> estart E (SA b off) = usp + d) -> d <= i < d + 8 -> FULL (Z_to_bv 64 (usp + i)) <> None).
{ intros b off v d Hk Hl Hst Hd.
destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off 8 v HC Hk)
as (_ & Hf & Hr & _).
rewrite (hb_adenot E _ _ Hf), (Hst Hf) in Hr.
apply (rdn_bytes_some ASEGS0 ASAN0 asan0_in_hull FULL _ 8 _ Hr).
- rewrite UX, u_small by lia. change (Z.of_nat 8) with 8. lia.
- rewrite UX. unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
destruct (Z_lt_le_dec i 24) as [C1|C1].
{
assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite g_sp0; reflexivity).
destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 L1 (ST 0)); lia|].
destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 L1 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 L1 (ST 16)); lia]. }
destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24)) as [C2|C2].
{
apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left.
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
destruct (Z_lt_le_dec i (Z.of_nat (cat_string_off rseq sp top argv envp execfn))) as [C3|C3].
{ destruct g_cparts as (LRB & LG & KU1 & KU2 & KU3).
pose proof g_w as UW. pose proof g_g as UG. pose proof g_chead as CH. pose proof g_gap as GR.
pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
assert (CS : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
= Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
by (unfold cat_string_off; lia).
assert (UNK : forall b k n s L, In (KUnk (SA b k) n) (kn cs) -> uE E b + k = usp + s ->
elenZ E n = L -> s <= i < s + L -> FULL (Z_to_bv 64 (usp + i)) <> None).
{ intros b k n s L Hin Hs HL Hi'.
destruct (hb_unk ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as (_ & Hd).
specialize (Hd (i - s) ltac:(lia)). rewrite hb_estart in Hd. unfold uE in Hs.
replace (bv_unsigned (edenot E b) + k + (i - s)) with (usp + i) in Hd by lia. exact Hd. }
assert (UA : uE E KE_AUX = usp + 8 * argc + 8 * envc).
{ unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA HUA. rewrite <- Es in HUA. lia. }
assert (EA : fst e_auxb = KE_AUX) by (vm_compute; reflexivity).
assert (EA2 : snd e_auxb = 24) by (vm_compute; reflexivity).
rewrite EA, EA2 in KU1, KU2. rewrite HRZ in KU1, KU2, KU3, CB, LRB.
pose proof (AsanInitK.e_atrb_off rseq) as RO.
change (snd (e_atrb (rseq_z rseq))) with (KE_RNDOFF (rseq_z rseq)) in RO.
assert (AX : AUXSZ (rseq_z rseq) = 432 + 32 * rseq_z rseq) by reflexivity.
assert (UR : uE E (KE_RND (rseq_z rseq)) = usp + 8 * argc + 8 * envc + 8 * Z.of_nat (block_items argv envp mod 2)).
{ revert LRB.
destruct (kb_rseq (in_kernel INP)); cbn [rseq_z]; intros LRB; unfold uE;
match goal with |- bv_unsigned (edenot E ?e) = _ =>
remember (bv_unsigned (edenot E e)) as xr eqn:Exr; LINEQ e LRB HRr; rewrite <- Exr in HRr end;
lia. }
assert (LGp : elenZ E (escale 8 (EVar V_G)) = 8 * Z.of_nat (block_items argv envp mod 2)).
{ unfold elenZ. remember (bv_unsigned (edenot E (escale 8 (EVar V_G)))) as g eqn:Eg.
LINEQ (escale 8 (EVar V_G)) LG HG. rewrite <- Eg in HG. lia. }
assert (L1A : elenZ E (ELit (AUXSZ (rseq_z rseq))) = AUXSZ (rseq_z rseq)).
{ unfold elenZ. cbn [edenot]. pose proof (rseq_z_range rseq). apply u64_lit. lia. }
assert (LW : elenZ E (EVar V_W) = Z.of_nat (block_pad_len rseq sp top argv envp execfn)) by exact UW.
destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24 + AUXSZ (rseq_z rseq))) as [D1|D1].
{ apply (UNK KE_AUX 24 (ELit (AUXSZ (rseq_z rseq))) (8 * argc + 8 * envc + 24) (AUXSZ (rseq_z rseq)) KU1);
[lia | exact L1A | lia]. }
destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24 + AUXSZ (rseq_z rseq) + 8 * Z.of_nat (block_items argv envp mod 2)))
as [D2|D2].
{ apply (UNK KE_AUX (24 + AUXSZ (rseq_z rseq)) (escale 8 (EVar V_G))
(8 * argc + 8 * envc + 24 + AUXSZ (rseq_z rseq)) (8 * Z.of_nat (block_items argv envp mod 2)) KU2);
[lia | exact LGp | lia]. }
destruct (Z_lt_le_dec i (Z.of_nat (block_head_size rseq argv envp))) as [D3|D3].
{
pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB))
as (_ & _ & Hb).
assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
rewrite EL in Hb. specialize (Hb (i - (Z.of_nat (block_head_size rseq argv envp) - 16)) ltac:(lia)).
rewrite hb_estart in Hb. unfold uE in UR. rewrite UR in Hb.
match type of Hb with context [Z_to_bv 64 ?t] => replace t with (usp + i) in Hb by lia end.
rewrite (hb_mr_some ASAN0 argH E cs model FULL _ _ Hb). discriminate. }
apply (UNK (KE_RND (rseq_z rseq)) (KE_RNDOFF (rseq_z rseq) + 16) (EVar V_W)
(Z.of_nat (block_head_size rseq argv envp)) (Z.of_nat (block_pad_len rseq sp top argv envp execfn)) KU3);
[lia | exact LW | lia].
}
apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.
Corollary entg_stack_defined_top : forall tp, tp mod 4096 = 0 -> tp <= usp + 4096 ->
forall i, 0 <= i < tp - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
Proof.
intros tp Hm Hle i Hi. apply entg_stack_defined. destruct g_simg_top as (T1 & T2 & T3). pose proof g_bounds as GB.
assert (G : 8 * argc + 8 * envc + 482 <= Z.of_nat (length SIMGx)) by (eapply AsanInitK.bsb_ge; eassumption).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Theorem entg_str0_defined :
forall i, 0 <= i < L0 + 1 + 8 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr top argv envp execfn 0) + i)) <> None.
Proof.
intros i Hi. pose proof g_rng as SR. pose proof g_bounds as GB. pose proof g_str0_ge. pose proof g_str0_top. pose proof g_utop_hi.
destruct g_simg_top as (T1 & T2 & _).
destruct entg_str0 as (_ & Hu).
destruct Hvl as [Hfn _].
change (in_execfn INP) with execfn in Hfn.
assert (Hfnlen : 1 <= Z.of_nat (length execfn)).
{ destruct Hfn as [[Hp _]|[(ds & Hds & _)|(ds & rest & Hds & _)]];
[lia | rewrite Hds, length_app; cbn [length dev_fd_prefix]; lia | rewrite Hds, !length_app; cbn [length dev_fd_prefix]; lia]. }
assert (HL : L0 + 1 + Z.of_nat (length execfn) + 1 <= LSTR).
{ unfold launch_string_bytes.
pose proof (Zle_0_nat (length (flatten_strings envp))).
destruct argv as [|a t]; [cbn in GB; lia|]. cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia. }
set (q := bv_unsigned (cat_argv_ptr top argv envp execfn 0)) in *.
assert (UXq : bv_unsigned (Z_to_bv 64 (q + i)) = q + i) by (apply u_small; lia).
apply g_argH_defined; [rewrite UXq; lia|].
rewrite hbi_argH, g_sp0, UXq.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
apply andb_true_intro. split; [apply Z.leb_le; lia|].
apply Z.ltb_lt.
lia.
Qed.
Theorem entg_tid : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QE'?'4&QAvQO%211(=%63521'@'R:yR0%211'>&QG+1&R;r1%2271%5241+SoooO%7231%9231':'8y8%@11%311%511&QC&Q:&L&Q8&Q?vFvE%332O1vR4%6221vG%9221&R9+V]kVH%22Q01u4%@4?521(2&H%124O%32F1%Q@3F51%Q62M1qTJQ81%Q<2Q91p0Q>1").
Proof.
intros CT. unfold tid_chk in CT.
destruct (kfind_word (kn cs) (ELit 0) 0x66ecd8 4) as [v|] eqn:K2; [|discriminate].
exists (edenot E v).
pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC CT) as RG. cbn [kentry_ok] in RG.
split; [exact RG|].
eapply (ent_litcell sp brk0 rdraw argv envp uid hw fs); try eassumption. lia.
Qed.
End EntryG.
