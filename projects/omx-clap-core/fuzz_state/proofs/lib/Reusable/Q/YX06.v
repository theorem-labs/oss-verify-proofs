From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN03 YN02 YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN0b YN07 YN0a YN1y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW04 YW0e YW07 YW09 YY00 YX00 YX01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition wr_stk (r : YP09.region) : bool :=
(obase_eqb (r_base r) (Some aSP) && (r_wlo r =? -8256) && (r_whi r =? 0)) || (r_whi r <=? r_wlo r).
Lemma wr_stack_only E rs x : forallb wr_stk rs = true -> in_wrange E rs x ->
base_val E (Some aSP) - 8256 <= x < base_val E (Some aSP).
Proof.
intros F (r & Hin & Hx). rewrite forallb_forall in F. specialize (F r Hin). unfold wr_stk in F.
apply orb_prop in F as [F|F]; [|apply Z.leb_le in F; lia].
apply andb_prop in F as [F F3]. apply andb_prop in F as [F1 F2].
apply Z.eqb_eq in F2. apply Z.eqb_eq in F3. destruct (r_base r) as [b|]; [|discriminate].
cbn in F1. apply Nat.eqb_eq in F1. subst b. lia.
Qed.
Lemma wr_entry_mem k r : forallb wr_stk (entry_memS k r) = true.
Proof. destruct k, r; vm_compute; reflexivity. Qed.
Lemma wr_mid_mem k r b1 ge : k <> K3b -> forallb wr_stk (ss_mem (midS (SA k r (NMid b1 ge)))) = true.
Proof. intros Hk. destruct k, r, b1, ge; (contradiction || vm_compute; reflexivity). Qed.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation E := (ES L regs g am idx fr a rg n).
Local Abbreviation XV := (xvS L regs g am idx fr a rg n).
Local Abbreviation PP := (ptr_addr L (frame_ptr am idx fr)).
Lemma XR6 : forall k, 0 <= XV k < 2 ^ 64.
Proof using HC. exact (XS L A regs mem md g am idx fr n a ka rg HC). Qed.
Lemma den_regS i : (1 <= i <= 31)%nat -> sv_denot E (SOff i 0) = getr regs (nat_to_reg i).
Proof using HC. intros Hi. unfold ES. rewrite (den_off0 _ XR6). rewrite XS_reg by lia. apply Z_to_bv_bv_unsigned. Qed.
Lemma base_SPS : base_val E (Some aSP) = spZ regs.
Proof using HC. unfold ES. rewrite (base_val_EV _ XR6). apply XS_SP. Qed.
Lemma PREs : YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\ alloc_ceiling + 8256 <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall x, spZ regs - 8256 <= x < spZ regs -> writable_at src0segs mem x) /\ getr regs 4 = Z_to_bv 64 src0_tp /\
(forall x, errno_addr src0_msyms <= x < errno_addr src0_msyms + 4 -> writable_at src0segs mem x).
Proof using HC.
pose proof (sx_pre _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
unfold REALLOC_STACK, ALLOC_STACK in *. repeat split; auto.
Qed.
Lemma den_ENDRS : sv_denot E (ENDR (rcase_of (reserved_of am fr))) = Z_to_bv 64 (PP + fr_n fr).
Proof using HC.
pose proof (FPS L A regs mem md g am idx fr n a ka rg HC) as FP.
pose proof (fp_r _ _ _ _ FP) as R. pose proof (lin_facts _ _ _ _ FP) as LF. cbn zeta in LF.
pose proof XR6 as XR.
assert (Eend : fv_end (vS L regs g am idx fr a rg) = PP + fr_n fr + reserved_of am fr).
{ unfold vS, fv_of. cbn [fv_end]. unfold slot_end, frame_ptr, reserved_of. rewrite !ptr_addr_padd'. lia. }
assert (Epn : fv_pn (vS L regs g am idx fr a rg) = PP + fr_n fr) by reflexivity.
assert (XE : XV aEND = fv_end (vS L regs g am idx fr a rg)) by reflexivity.
assert (XPN : XV aPN = fv_pn (vS L regs g am idx fr a rg)) by reflexivity.
assert (Ersv : fv_rsv (vS L regs g am idx fr a rg) = reserved_of am fr) by reflexivity.
clear FP. unfold rcase_of in *. unfold ES.
destruct (reserved_of am fr =? 0) eqn:E0; [| destruct (reserved_of am fr <? 5) eqn:E1; [| destruct (reserved_of am fr =? 5) eqn:E2]]; cbn [ENDR].
- apply Z.eqb_eq in E0. rewrite (den_off0 _ XR). rewrite XE. f_equal. lia.
- rewrite (den_off0 _ XR). rewrite XPN, Epn. reflexivity.
- apply Z.eqb_eq in E2. rewrite (den_off _ XR); [rewrite XE; f_equal; lia|]. rewrite XE. unfold CEIL in LF. lia.
- rewrite (den_off0 _ XR). rewrite XPN, Epn. reflexivity.
Qed.
Lemma errno_lowS x : errno_addr src0_msyms <= x < errno_addr src0_msyms + 4 -> 0 <= x < 2 ^ 64 /\ x < alloc_ceiling.
Proof using.
intros Hx. change (errno_addr src0_msyms) with ERRNO2 in Hx. rewrite ERRNO2_val in Hx. unfold src0_tp in Hx.
pose proof YM05.alloc_ceiling_val as HCV. lia.
Qed.
Theorem arrival_fbS ss4 ms4 :
st_ok src0segs E ss4 ms4 -> ss_pc ss4 = src0_A_libc_malloc_impl -> ss_resv ss4 = None ->
view MV ss4 = arr_view (rcase_of (reserved_of am fr)) -> In stk1 (ss_mem ss4) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8256 <= x < spZ regs) -> ms_mem ms4 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ms4 = mkst (ms_regs ms4) (Z_to_bv 64 src0_A_libc_malloc_impl) (ms_mem ms4) (seg_rom src0segs) /\
fb_arrival L A regs mem md (frame_ptr am idx fr) (fr_n fr) n (ms_regs ms4) (ms_mem ms4).
Proof using HC.
intros HS Hpc Hrv Hv Hstk RAW.
pose proof (st_ok_mkst src0segs _ _ _ HS Hrv) as SH. rewrite Hpc in SH.
split; [exact SH|].
pose proof PREs as (Hret & Hal & Hceil & Hsp63 & Hstkw & Htp & Herrw).
pose proof YM05.alloc_ceiling_lt as HCL. pose proof YM05.alloc_ceiling_val as HCV0.
pose proof (st_ok_regs_ok src0segs E _ _ HS) as R.
unfold view, arr_view in Hv. cbn [map MV] in Hv.
vnth Hv 0%nat V1. vnth Hv 1%nat V2. vnth Hv 2%nat V3. vnth Hv 3%nat V4. vnth Hv 4%nat V8. vnth Hv 5%nat V9. vnth Hv 6%nat V10.
vnth Hv 7%nat V18. vnth Hv 12%nat V23. vnth Hv 13%nat V24. vnth Hv 14%nat V25. vnth Hv 15%nat V26. vnth Hv 16%nat V27.
pose proof (st_ok_mem_ok src0segs E _ _ HS) as (_ & ROK & _).
pose proof (proj1 (Forall_forall _ _) ROK stk1 Hstk) as (_ & _ & Wst & Cst).
cbn [r_base r_wlo r_whi r_chunks stk1] in Wst, Cst. rewrite base_SPS in Wst, Cst.
assert (XN : XV aN = n) by exact (XS_N L A regs mem md g am idx fr n a ka rg HC).
assert (XP : XV aP = PP) by exact (XS_P L A regs mem md g am idx fr n a ka rg HC).
split.
- exact (sx_pre _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact (sx_in _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact (sx_a0 _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact (sx_a1 _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
- rewrite (R 1%bv), V1. reflexivity.
- rewrite (R 2%bv), V2. unfold ES. rewrite (den_off _ XR6); [rewrite XS_SP; reflexivity|]. rewrite XS_SP. lia.
- rewrite (R 8%bv), V8. unfold ES. rewrite (den_off0 _ XR6), XN. reflexivity.
- rewrite (R 9%bv), V9. unfold ES. rewrite (den_off0 _ XR6), XP. reflexivity.
- rewrite (R 10%bv), V10. unfold ES. rewrite (den_off0 _ XR6), XN. reflexivity.
- rewrite (R 18%bv), V18. exact den_ENDRS.
- intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [nat_to_reg];
[rewrite (R 3%bv), V3 | rewrite (R 4%bv), V4 | rewrite (R 23%bv), V23 | rewrite (R 24%bv), V24
| rewrite (R 25%bv), V25 | rewrite (R 26%bv), V26 | rewrite (R 27%bv), V27];
apply den_regS; lia.
- assert (FCB : forall o rr i, In (mkChunk o (CVal 8 (SOff rr 0))) frame_chunks -> (1 <= rr <= 31)%nat -> 0 <= i < 8 ->
mbyte src0segs (ms_mem ms4) (spZ regs + o + i) = Some (byte_of_word (getr regs (nat_to_reg rr)) i)).
{ intros o rr i Hc Hr Hi. destruct (proj1 (Forall_forall _ _) Cst _ Hc i ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [c_off c_val cbyte] in Hb, Hm. rewrite Hm, <- Hb. rewrite den_regS by exact Hr. reflexivity. }
intros o rr i Hin Hi. unfold FB_SLOTS in Hin.
destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <-;
(apply FCB; [unfold frame_chunks; cbn [In]; repeat (first [left; reflexivity | right]) | lia | exact Hi]).
- intros x Hx. unfold fb_stk, REALLOC_STACK, ALLOC_STACK in Hx. replace x with (spZ regs + (x - spZ regs)) by lia. apply Wst. lia.
- intros x Hx. unfold fb_errno in Hx. pose proof (errno_lowS x Hx) as [X1 X2].
apply (proj1 (proj2 (same_views src0segs mem (ms_mem ms4) x (RAW x X1 ltac:(lia))))). apply Herrw. exact Hx.
- intros x Hx N1 N2. apply RAW; [exact Hx|]. unfold fb_stk, REALLOC_STACK, ALLOC_STACK in N1. lia.
Qed.
End b.
End a.
