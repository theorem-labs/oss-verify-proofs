(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/DecodeARowsRt.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* libreac/fuzz_decode image A (fuzz_decode.asan): proofs of three premise rows of the closing composition
   lib/A/DecodeClose.v, the three small runtime entries the calloc interceptor calls before the allocator.  Each
   lemma has the type of the DecodeClose.v hypothesis it names:

     dec_a_rt_try   : H_CALLOC_RT_TRY   (DecodeClose.v:250)  decode_try_init_spec_A  (DecodeCallocRt.v:332)
     dec_a_rt_mcs   : H_CALLOC_RT_MCS   (DecodeClose.v:251)  decode_mcs_spec_A       (DecodeCallocRt.v:333)
     dec_a_rt_getpc : H_CALLOC_RT_GETPC (DecodeClose.v:252)  decode_getpc_spec_A     (DecodeCallocRt.v:334)

   Each proof runs the function's own words through the symbolic executor (lib/Reusable/YP0l.v sym_step, by the
   lib/Reusable/YA0o.v walk tactics srr_run_with / SRr_ret_at, as lib/A/AFl4.v:355-411 exit_ok uses them) from a
   seed state built from the contract's premises, up to the function's `ret`.  The words are read out of the image
   ([tbl_rt_A], DecodeCallocTbl.v build_ranges over decodesegs0).  The window and frame lemmas are
   lib/A/DecodeCallocWrap.v's (st_ok_window_apresent_high, lit1) and lib/A/DecodeCallocSeed.v's (decode_wx).

   The code, from fuzz_decode.objdump.txt (image A, the pinned
   fuzz_decode.asan; the symbol table's sizes are DecodeCallocRt.v:35-37):

     __asan::TryAsanInitFromRtl, 0x590ac (160 bytes, 40 instructions; the run takes the first 13):
       590ac: ff010113  addi sp,sp,-16          590b0: 00113423  sd ra,8(sp)        590b4: 00813023  sd s0,0(sp)
       590b8: 00049517  auipc a0,0x49           590bc: 9e050413  addi s0,a0,-1568   (s0 = 0xa1a98, asan_inited)
       590c0: 00040583  lb a1,0(s0)             590c4: 00100513  li a0,1            590c8: 0230000f  fence r,rw
       590cc: 00a59a63  bne a1,a0,590e0         (not taken: the byte is 1)
       590d0: 00813083  ld ra,8(sp)             590d4: 00013403  ld s0,0(sp)        590d8: 01010113  addi sp,sp,16
       590dc: 00008067  ret
     __asan::GetMallocContextSize, 0x59e34 (16 bytes, 4 instructions):
       59e34: 00048517  auipc a0,0x48           59e38: c8852503  lw a0,-888(a0)     (0xa1abc, malloc_context_size)
       59e3c: 0230000f  fence r,rw              59e40: 00008067  ret
     __sanitizer::StackTrace::GetCurrentPc, 0x72a08 (8 bytes, 2 instructions):
       72a08: 00008513  mv a0,ra                72a0c: 00008067  ret

   The seeds.  Every register is its own atom (atom i is x_i at the entry, YI04.v:78 Ereg).  GetCurrentPc reads no
   memory, so its seed has no region.  GetMallocContextSize's seed has one read-only region, the 4-byte cell
   DEC_A_malloc_context_size holding atom 32 = the contract's v, with the atom fact 0 <= v < 2 ^ 31 (so `lw`'s sign
   extension is v).  TryAsanInitFromRtl's seed has the 16-byte stack window [sp - TAI_STK, sp) (writable, from the
   presence premise) and the read-only byte DEC_A_asan_inited = 1 (the contract's val_mem premise); the window is
   above YImgTop.IMG_TOP (the premise IMG_TOP <= sp - TAI_STK), so the two are disjoint.  No Axiom, Parameter or
   Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import
YB1v DecodeCallocTbl DecodeCalloc DecodeCallocSkel DecodeCallocSeed DecodeCallocRt DecodeCallocWrap.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YN2j YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import CallocImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The three functions' words, read out of image A.  The instruction counts are the symbol table's sizes / 4
   (DecodeCallocRt.v:35-37: 160, 16 and 8 bytes). *)
Definition rt_ranges_A : list (Z * nat) :=
[ (DEC_A_TryAsanInitFromRtl, 40%nat); (DEC_A_GetMallocContextSize, 4%nat); (DEC_A_GetCurrentPc, 2%nat) ].
Definition tbl_rt_A : ctable := Eval vm_compute in build_ranges tfibsegs rt_ranges_A TEmpty.
Lemma tbl_rt_A_eq : tbl_rt_A = build_ranges tfibsegs rt_ranges_A TEmpty.
Proof. vm_cast_no_check (@eq_refl ctable tbl_rt_A). Qed.
Lemma tbl_rt_A_ok : table_ok tfibsegs tbl_rt_A.
Proof.
rewrite tbl_rt_A_eq. apply build_ranges_ok; [repeat constructor; cbv; intros Hx; discriminate Hx | apply table_ok_empty].
Qed.

(* The seeds (see the header). *)
Definition SS_PC0 : sstate := mkSS DEC_A_GetCurrentPc sr_atoms [] None (mkFacts [] [] []).
Definition R_MCS : YP09.region :=
YP09.mkRegion None DEC_A_malloc_context_size (DEC_A_malloc_context_size + 4) 0 0
[YP09.mkChunk DEC_A_malloc_context_size (CVal 4 (SOff 32 0))].
Definition F_MCS : facts := mkFacts [(32%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] [].
Definition SS_M0 : sstate := mkSS DEC_A_GetMallocContextSize sr_atoms [R_MCS] None F_MCS.
Definition R_TS : YP09.region := YP09.mkRegion (Some 2%nat) (- TAI_STK) 0 (- TAI_STK) 0 [].
Definition SS_T0 : sstate :=
mkSS DEC_A_TryAsanInitFromRtl sr_atoms [R_TS; lit1 DEC_A_asan_inited 1] None (mkFacts [] [] []).

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma writable_of_apresent : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> writable_at tfibsegs (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma apresent_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a He [Hh Hb]. split; [exact Hh|]. rewrite He. exact Hb. Qed.

(* A read-only region over one cell of w bytes holding e's value v (cgif A/AFl3.v:72 region_ok_lit, with any
   value expression). *)
Lemma region_ok_litw : forall E (m : word -> option byte) a (w : N) e v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> 0 <= a -> a + Z.of_N w <= 2 ^ 64 ->
val_mem tfibsegs m a (N.to_nat w) v ->
region_ok tfibsegs E m (YP09.mkRegion None a (a + Z.of_N w) 0 0 [YP09.mkChunk a (CVal w e)]).
Proof.
intros E m a w e v He Hv Hw Ha Hh Hm. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [exact He | exact Hv | exact Hw | rewrite Z.add_0_l; exact Hm].
Qed.

(* ------------------------------------------------------------------------------------------------------------
   StackTrace::GetCurrentPc. *)
Lemma getpc_ok : getpc_specP tfibsegs DEC_A_GetCurrentPc.
Proof.
unfold getpc_specP. intros W regs mem md HRA.
pose proof decode_wx as Hwx.
assert (ER1 : ew (Ereg regs []) 1 = YK11.getr regs 1) by exact (ew_Ereg_nat regs [] 1 1%bv eq_refl).
assert (HS : st_ok tfibsegs (Ereg regs []) SS_PC0
(restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 DEC_A_GetCurrentPc) mem (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_PC0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; exact I]. }
srr_run_with tbl_rt_A_ok HS.
eapply (SRr_ret_at tfibsegs tbl_rt_A tbl_rt_A_ok Hwx W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite ?wvb_collapse. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msf) => exists (ms_regs msf), (ms_mem msf), mat' end.
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
split. { rewrite Q1, ER1. unfold YK0s.ret_ok in HRA. rewrite HRA. reflexivity. }
split. { exact (regs_preserved_of_st_ok tfibsegs (Ereg regs []) _ _ regs [] HS (env_agree_refl 32 _)
ltac:(vm_compute; reflexivity)). }
split. { rewrite Q10. exact ER1. }
intros x. apply HF. intros (r & Hin & _). exact Hin.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   GetMallocContextSize. *)
Lemma mcs_ok : mcs_specP tfibsegs DEC_A_GetMallocContextSize DEC_A_malloc_context_size.
Proof.
unfold mcs_specP. intros W regs mem md v. cbv zeta. intros HRA HV Hv.
pose proof decode_wx as Hwx.
assert (ER1 : ew (Ereg regs [Z_to_bv 64 v]) 1 = YK11.getr regs 1)
by exact (ew_Ereg_nat regs [Z_to_bv 64 v] 1 1%bv eq_refl).
assert (E32 : ew (Ereg regs [Z_to_bv 64 v]) 32 = Z_to_bv 64 v) by reflexivity.
assert (D32 : sv_denot (Ereg regs [Z_to_bv 64 v]) (SOff 32 0) = Z_to_bv 64 v).
{ cbn [sv_denot]. rewrite E32, unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
assert (HS : st_ok tfibsegs (Ereg regs [Z_to_bv 64 v]) SS_M0
(restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 DEC_A_GetMallocContextSize) mem (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_M0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply Forall_nil].
apply (region_ok_litw _ _ DEC_A_malloc_context_size 4%N (SOff 32 0) v);
[exact D32 | cbn; lia | cbn; lia | unfold DEC_A_malloc_context_size; lia
| unfold DEC_A_malloc_context_size; cbn; lia | exact HV].
- split; [exact I | split; exact I].
- unfold F_MCS. split; [| split; exact I]. cbn [f_atoms atoms_ok]. split; [| exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia. }
srr_run_with tbl_rt_A_ok HS.
eapply (SRr_ret_at tfibsegs tbl_rt_A tbl_rt_A_ok Hwx W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite ?wvb_collapse. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msf) => exists (ms_regs msf), (ms_mem msf), mat' end.
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
split. { rewrite Q1, ER1. unfold YK0s.ret_ok in HRA. rewrite HRA. reflexivity. }
split. { exact (regs_preserved_of_st_ok tfibsegs (Ereg regs [Z_to_bv 64 v]) _ _ regs [Z_to_bv 64 v] HS
(env_agree_refl 32 _) ltac:(vm_compute; reflexivity)). }
split. { rewrite Q10. exact E32. }
intros x. apply HF. intros (r & Hin & Hr). cbn [ss_mem SS_M0 In] in Hin.
destruct Hin as [<- | []]. cbn [base_val R_MCS YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   TryAsanInitFromRtl. *)
Lemma try_ok : try_init_specP tfibsegs DEC_A_TryAsanInitFromRtl DEC_A_asan_inited.
Proof.
unfold try_init_specP. intros W regs mem md. cbv zeta. intros HRA HAL HTOP HPRES HV.
pose proof decode_wx as Hwx. pose proof IMG_TOP_val as IT. assert (TS : TAI_STK = 16) by reflexivity.
pose proof (u64_range (YK11.getr regs 2)) as SPR.
assert (ER1 : ew (Ereg regs []) 1 = YK11.getr regs 1) by exact (ew_Ereg_nat regs [] 1 1%bv eq_refl).
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = bv_unsigned (YK11.getr regs 2))
by (rewrite (ew_Ereg_nat regs [] 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok tfibsegs (Ereg regs []) SS_T0
(restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 DEC_A_TryAsanInitFromRtl) mem (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_T0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
+ apply (region_ok_stack tfibsegs (Ereg regs []) _ 2%nat (bv_unsigned (YK11.getr regs 2)) (- TAI_STK) E2).
* lia.
* lia.
* intros a Ha. apply writable_of_apresent. apply HPRES. lia.
+ apply (region_ok_litw _ _ DEC_A_asan_inited 1%N (SLit 1) 1);
[reflexivity | cbn; lia | cbn; lia | unfold DEC_A_asan_inited; lia
| unfold DEC_A_asan_inited; cbn; lia | exact HV].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_TS, lit1.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold TAI_STK, DEC_A_asan_inited in *. repeat split; lia.
- split; [exact I | split; exact I]. }
srr_run_with tbl_rt_A_ok HS.
eapply (SRr_ret_at tfibsegs tbl_rt_A tbl_rt_A_ok Hwx W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite ?wvb_collapse. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msf) => exists (ms_regs msf), (ms_mem msf), mat' end.
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
split. { rewrite Q1, ER1. unfold YK0s.ret_ok in HRA. rewrite HRA. reflexivity. }
split. { exact (regs_preserved_of_st_ok tfibsegs (Ereg regs []) _ _ regs [] HS (env_agree_refl 32 _)
ltac:(vm_compute; reflexivity)). }
split. { exact Q10. }
(* The run wrote only the stack window. *)
assert (WIN : forall a, in_wrange (Ereg regs []) (ss_mem SS_T0) a ->
bv_unsigned (YK11.getr regs 2) - TAI_STK <= a < bv_unsigned (YK11.getr regs 2)).
{ intros a Ha. pose proof (in_wrange_single_b (Ereg regs []) (ss_mem SS_T0) a 2%nat (- TAI_STK) 0
(bv_unsigned (YK11.getr regs 2)) ltac:(vm_compute; reflexivity) E2 Ha). lia. }
split.
{ intros x Hx. apply HF. intros Hw. apply Hx. exact (WIN _ Hw). }
intros a Ha.
set (x := Z_to_bv 64 a). assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
pose proof (u64_range x) as XR.
destruct (Z_le_gt_dec (bv_unsigned (YK11.getr regs 2) - TAI_STK) (bv_unsigned x)) as [L1 | L1];
[destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (YK11.getr regs 2))) as [L2 | L2] |].
- lazymatch type of HS with st_ok _ _ _ (restrict _ ?msf) =>
assert (P : apresent (w_H W) (ms_mem msf) (bv_unsigned x)) end.
{ eapply (st_ok_window_apresent_high (w_H W) _ _ _ 0%nat); [exact HS | reflexivity | |].
- cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite E2. lia.
- lia. }
unfold apresent in P |- *. rewrite Ex in P. exact P.
- apply (apresent_eq (w_H W) mem); [| exact Ha]. fold x. apply HF. intros Hw. pose proof (WIN _ Hw). lia.
- apply (apresent_eq (w_H W) mem); [| exact Ha]. fold x. apply HF. intros Hw. pose proof (WIN _ Hw). lia.
Qed.

End s.

(* ------------------------------------------------------------------------------------------------------------
   The rows, in DecodeClose.v's form. *)
Lemma dec_a_rt_try : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_try_init_spec_A.
Proof. intros fx rc. exact try_ok. Qed.
Lemma dec_a_rt_mcs : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_mcs_spec_A.
Proof. intros fx rc. exact mcs_ok. Qed.
Lemma dec_a_rt_getpc : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_getpc_spec_A.
Proof. intros fx rc. exact getpc_ok. Qed.
