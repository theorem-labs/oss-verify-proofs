(* SCRATCH (piece R6 of a Theorem Labs lane): SEG3 of put_string's closing theorem (ZZpsclose.ps_close's third premise), image A
   (fs.asan): from put #2's return PS_END_RET, the stretch to the closing-quote put (ZZpsjoin.psj_put2_put3), the put
   call itself (FSW_put_string.ps_put_call with src = PS_Q1, n = 1), and its return rebuilt as the epilogue's state
   (ZZpsres.psr_resume_epi), carried in ps_inv over the three pieces [[34]; bs; [34]].
   Helpers by import: ZZpsg1k (ps_quote_src, ps_heads_put), ZZpsg2k (psk_chain_o, psk_fp_rel,
   psk_wout_blk, psk_aru_pre, psk_arodata_ret), ZZpsg3k (ps_chain_call, ps_chain_agree, ps_str_keep, the
   pointwise transports and the return-side moves). The model algebra is ZZpsmodel's (psm_wevk_step, psm_put1_eq,
   psm_wbudget_pre3, psm_wbudget_kept2, psm_uswap2_ar, psm_bswap2_ar). Folded into FSW_put_string.v by a Theorem Labs lane. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame
FSW_frame3 FSW_writer_tbl FSW_writer_model FSW_strkit FSW_writer_kit FSW_put_string ZZpsjoin ZZpskeep ZZpsmodel
ZZpssep ZZpsres ZZpsclose ZZpsg1k ZZpsg2k ZZpsg3k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterRet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic (lia only here) ================= *)
Lemma psg3_arith : forall sp0 sp1 o ot ac,
  sp0 mod 16 = 0 -> ac + STK_put_string <= sp0 -> 0x7fff7f800000 <= ac -> sp0 <= o -> o + 32 <= ot ->
  ot mod 16 = 0 -> ot <= 2 ^ 47 -> sp1 = 32 * ((sp0 - PS_FRAME_OWN) / 32) ->
  sp1 mod 32 = 0 /\ sp1 + 192 <= sp0 /\ 0 <= sp1 < 2 ^ 64 /\
  (sp1 - ot) mod 16 = 0 /\ sp1 - ot <= 0 /\ STK_put - (sp1 - ot) <= STK_put_string + (ot - sp0) /\
  ot - (STK_put_string + (ot - sp0)) <= sp0 + -104 /\
  ot - (STK_put_string + (ot - sp0)) <= ot - (STK_put + (ot - sp1)) /\
  ot - (STK_put_string + (ot - sp0)) <= sp1 /\
  sp1 <= sp0 + -104 /\ sp0 + 0 <= ot /\ sp1 <= ot /\ sp1 + 16 <= sp0 /\ ac <= sp1 /\ sp1 <= sp0 /\
  0 <= o < 2 ^ 64 /\ 0 <= sp0 < 2 ^ 64 /\ PS_Q1 + 1 <= o /\ sp0 <= ot /\ sp0 + 0 <= o /\ sp1 <= o /\
  sp0 + 8 <= ot /\ 0 <= sp0 - 16.
Proof.
intros sp0 sp1 o ot ac H16 Hac Hac0 Ho Hoot Hot H47 E.
assert (ES : STK_put_string = ltac:(let v := eval vm_compute in STK_put_string in exact v))
  by (vm_compute; reflexivity).
assert (EP : STK_put = ltac:(let v := eval vm_compute in STK_put in exact v)) by (vm_compute; reflexivity).
rewrite ES in *. rewrite EP. unfold PS_FRAME_OWN, PS_Q1 in *. subst sp1.
Z.div_mod_to_equations. lia.
Qed.

Lemma psg3_peak : forall peak peak2 peak3 live cap c2 c3,
  c2 <= c3 ->
  peak <= peak2 <= Z.max peak (live - cap + c2) ->
  peak2 <= peak3 <= Z.max peak2 (live + c2 - cap - c2 + c3) ->
  peak <= peak3 <= Z.max peak (live - cap + c3).
Proof. intros. lia. Qed.

(* ================= the model of the third piece ================= *)
(* the count after three pieces is the count after two plus the third call's own *)
Lemma psg3_wevk3 : forall failed text cap cnt fail (bs : list Z),
  FSH_Fn_writer.wevk cap (ps_st failed text cap cnt fail [[34]; bs; [34]]) =
  FSH_Fn_writer.wevk cap (ps_st failed text cap cnt fail [[34]; bs]) +
  FSH_Fn_writer.wevk (WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs]))
    (WriterApp.put1 (psm_rs (ps_st failed text cap cnt fail [[34]; bs])) [34]).
Proof.
intros. unfold ps_st, WriterApp.putN. cbn [fold_left].
apply psm_wevk_step. apply psm_inv_step, psm_inv_step, psm_inv_init.
Qed.

(* the five fields after three pieces are the third call's *)
Lemma psg3_fields3 : forall failed text cap cnt fail (bs : list Z) (st' : WriterApp.wst),
  st' = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (ps_st failed text cap cnt fail [[34]; bs]))
          (WriterApp.w_text (ps_st failed text cap cnt fail [[34]; bs]))
          (WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs]))
          (WriterApp.w_cnt (ps_st failed text cap cnt fail [[34]; bs]))
          (WriterApp.w_fail (ps_st failed text cap cnt fail [[34]; bs])) []) [34] ->
  WriterApp.w_failed (ps_st failed text cap cnt fail [[34]; bs; [34]]) = WriterApp.w_failed st' /\
  WriterApp.w_text (ps_st failed text cap cnt fail [[34]; bs; [34]]) = WriterApp.w_text st' /\
  WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs; [34]]) = WriterApp.w_cap st' /\
  WriterApp.w_cnt (ps_st failed text cap cnt fail [[34]; bs; [34]]) = WriterApp.w_cnt st' /\
  WriterApp.w_fail (ps_st failed text cap cnt fail [[34]; bs; [34]]) = WriterApp.w_fail st'.
Proof.
intros failed text cap cnt fail bs st' ->.
assert (E : ps_st failed text cap cnt fail [[34]; bs; [34]] =
            WriterApp.put1 (ps_st failed text cap cnt fail [[34]; bs]) [34]) by reflexivity.
rewrite E, (psm_put1_eq (ps_st failed text cap cnt fail [[34]; bs]) [34]).
repeat split; reflexivity.
Qed.

(* the room premise of the third call, from put_string_spec's *)
Lemma psg3_wmax : forall failed text cap cnt fail (bs : list Z), plain_bytes bs ->
  Z.of_nat (length text) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= FSH_Fn_writer.WMAX ->
  Z.of_nat (length (WriterApp.w_text (ps_st failed text cap cnt fail [[34]; bs]))) + 1 + 1 <= FSH_Fn_writer.WMAX.
Proof.
intros failed text cap cnt fail bs Hp H. rewrite (wstr_plain bs Hp) in H.
pose proof (WriterRet.putN_text [[34]; bs] (WriterApp.mkW failed text cap cnt fail [])) as T.
unfold ps_st. cbn [concat app length WriterApp.w_text] in T, H.
rewrite ?length_app in H, T. cbn [length] in H, T. lia.
Qed.

(* the budget premise of the third call, from put_string_spec's and what the walk holds after two pieces *)
Lemma psg3_bp : forall S S2 failed text cap cnt fail live (bs : list Z) k2,
  plain_bytes bs -> 0 <= cap -> 0 <= cnt ->
  FSH_Fn_writer.wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) ->
  k2 = FSH_Fn_writer.wevk cap (ps_st failed text cap cnt fail [[34]; bs]) ->
  st_nev S2 <= st_nev S + k2 ->
  FSH_Fn_writer.wbudget_kept S S2 failed cap cnt
    (WriterApp.w_failed (ps_st failed text cap cnt fail [[34]; bs]))
    (WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs]))
    (WriterApp.w_cnt (ps_st failed text cap cnt fail [[34]; bs])) ->
  FSH_Fn_writer.wbudget_pre S2 (WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs]))
    (WriterApp.w_cnt (ps_st failed text cap cnt fail [[34]; bs]))
    (live + WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs]) - cap)
    (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (ps_st failed text cap cnt fail [[34]; bs]))
       (WriterApp.w_text (ps_st failed text cap cnt fail [[34]; bs]))
       (WriterApp.w_cap (ps_st failed text cap cnt fail [[34]; bs]))
       (WriterApp.w_cnt (ps_st failed text cap cnt fail [[34]; bs]))
       (WriterApp.w_fail (ps_st failed text cap cnt fail [[34]; bs])) []) [34]).
Proof.
intros S S2 failed text cap cnt fail live bs k2 Hp Hc Hn HB Ek Hnev HK.
set (s1 := WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34]).
set (s2 := WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
             (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs).
assert (E2 : ps_st failed text cap cnt fail [[34]; bs] = WriterApp.put1 s1 bs) by reflexivity.
pose proof (psm_put1_eq s1 bs) as EP.
assert (F : WriterApp.w_failed (WriterApp.put1 s1 bs) = WriterApp.w_failed s2 /\
            WriterApp.w_text (WriterApp.put1 s1 bs) = WriterApp.w_text s2 /\
            WriterApp.w_cap (WriterApp.put1 s1 bs) = WriterApp.w_cap s2 /\
            WriterApp.w_cnt (WriterApp.put1 s1 bs) = WriterApp.w_cnt s2 /\
            WriterApp.w_fail (WriterApp.put1 s1 bs) = WriterApp.w_fail s2)
  by (rewrite EP; repeat split; reflexivity).
destruct F as (Ff & Ft & Fc & Fn & Fl).
assert (Ek' : k2 = FSH_Fn_writer.wevk cap s1 + FSH_Fn_writer.wevk (WriterApp.w_cap s1) s2).
{ rewrite Ek, E2. exact (psm_wevk_step cap s1 bs (psm_inv_step cap _ [34] (psm_inv_init failed text cap cnt fail))). }
rewrite E2 in HK |- *. rewrite Ff, Ft, Fc, Fn, Fl. rewrite Ff, Fc, Fn in HK.
destruct HK as (_ & Hbb & _).
exact (psm_wbudget_pre3 S S2 failed text cap cnt fail live (live + WriterApp.w_cap s1 - cap)
  (live + WriterApp.w_cap s2 - cap) bs s1 s2 _ Hp Hc Hn eq_refl eq_refl eq_refl HB eq_refl
  ltac:(ring) ltac:(clear - Hnev Ek'; lia) Hbb).
Qed.

(* a callee-saved register read across the call *)
Lemma psg3_pres : forall regs regs' (r : bv 5) z, aregs_preserved regs regs' -> acallee_saved z ->
  r = Z_to_bv 5 z -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz ->. exact (HP z Hz). Qed.

Section G3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* put's contract (FSW_put_string's Section hypothesis HPUT, ps_put_call's only one) and fs's image facts (the quote
   string's and the table string's facts, FSW_strkit.cstr_ok_kept_tbl) *)
Hypothesis HPUT : FSH_Fn_writer.put_spec B tfibsegs.
Hypothesis HIMG : fs_img_facts tfibsegs B.
#[local] Abbreviation ps_pre := (ZZpsclose.ps_pre B).
#[local] Abbreviation ps_inv := (ZZpsclose.ps_inv B).

(* ================= SEG3 (ZZpsclose.ps_close's third premise, verbatim) ================= *)
Lemma psg3 :
  (forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     pos lyc ly2 S2 U2 W2 regs2 mem2 md2 buf2 (Q : world tfibsegs -> config -> Prop),
   ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
     [[34]; bs] PS_END_RET (ps_ret_ss PS_END_RET (Z.of_nat (length bs)) psj_scs0 [])
     ly2 S2 U2 W2 regs2 mem2 md2 buf2 ->
   (forall ly3 S3 U3 W3 regs3 mem3 md3 buf3,
      ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
        [[34]; bs; [34]] PS_CLOSE_RET (ps_epi_ss PS_CLOSE_RET)
        ly3 S3 U3 W3 regs3 mem3 md3 buf3 ->
      SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 PS_CLOSE_RET) mem3 (seg_rom tfibsegs)) md3) Q) ->
   SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 PS_END_RET) mem2 (seg_rom tfibsegs)) md2) Q).
Proof.
intros ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail
  pos lyc ly2 S2 U2 W2 regs2 mem2 md2 buf2 Q PRE INV KONT.
pose proof PRE as (HPRE & Hheads & Hfr & G10 & G11 & HOUT & HGLOB & HHEAD & Hspo & Hoot & Hot16 & Hottop & Hcho &
  HFPc & HPRES & Hcstr & Hsrck & Hbok & Hnz & Hplain & Hsep & Hwmax & Hcap & Hlive & Hbp).
unfold ZZpsclose.ps_inv in INV. cbv zeta in INV.
destruct INV as (Hin2 & Efr2 & -> & HJ2 & HARU2 & HS2 & _ & R2 & R8 & R9 & R19 & R21 & R22 & R23 & R24 & R26 & R3 & R4 &
  H80 & Hhdr & Hfsh & Hus2 & HOUT2 & HBK2 & HBS2 & HKEEP2 & Hcstr2 & (peak2 & Hpk2 & HGLOB2) & Hsrc2 & HHD2 &
  Hheads2 & HRO2 & HPR2).
(* ---- the entry ---- *)
pose proof (psk_aru_pre B STK_put_string ly S U W regs mem md ch HPRE) as HARU0.
pose proof HPRE as (((HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & _ & _ & _) & _ & _) & HRO0).
pose proof Hstk0 as (Hal16 & _ & Hceilo & Hslo & _ & H47s & _ & _ & Htop2).
pose proof (fsw_sp B STK_put_string ly S U W regs mem md ch (proj1 HPRE)) as (_ & Hceil & _ & _).
assert (Hot47 : ot <= 2 ^ 47) by (clear - Hottop Htop2 H47s; lia).
pose proof (psk_wout_blk B ly S W mem o buf cap failed text HOUT) as (Hblk0 & _).
assert (Hcap0 : 0 <= cap) by (destruct HOUT as (_ & _ & _ & _ & _ & (Hc & _) & _); exact Hc).
assert (Hcnt0 : 0 <= cnt) by (destruct HGLOB as (_ & _ & _ & _ & _ & _ & (Hc & _) & _); exact Hc).
set (sp0 := spZ regs) in *.
set (sp1 := 32 * ((sp0 - PS_FRAME_OWN) / 32)) in *.
destruct (psg3_arith sp0 sp1 o ot alloc_ceiling Hal16 Hceil (proj1 (proj1 asan_consts)) Hspo Hoot Hot16 Hot47
            eq_refl)
  as (A32 & A192 & A64 & Aoff16 & Aoff0 & Abud & Awin104 & Awin & Ajt & Alo104 & Ahi & Asp1ot & A16 & Aac & Asp10 &
      Ao64 & Asp064 & Aq1 & Asp0ot & Asp0o & Asp1o & Asp08 & Asp016).
set (F := frame_addr ly 0 pos) in *.
set (FL := flag_addr ly 0 pos) in *.
set (X := fs_extraT ++ ps_xs regs FL ++ [Z_to_bv 64 (shadow_addr F)]) in *.
set (st2 := ps_st failed text cap cnt fail [[34]; bs]) in *.
set (FPw := FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) in *.
set (k2 := FSH_Fn_writer.wevk cap st2) in *.
set (STKw := STK_put_string + (ot - sp0)) in *.
(* ---- the layout after the first two pieces keeps the fake stack and the top ---- *)
pose proof HJ2 as (_ & LLE2 & _).
destruct LLE2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & Etop2 & _).
assert (EFa2 : frame_addr ly2 0 pos = F) by (unfold F, frame_addr; rewrite EF2; reflexivity).
pose proof (psk_wout_blk B ly2 S2 W2 mem2 o buf2 _ _ _ HOUT2) as (Hblk2 & Hb2z).
assert (Hcm2 : cap <= WriterApp.w_cap st2)
  by exact (WriterRet.putN_cap [[34]; bs] (WriterApp.mkW failed text cap cnt fail []) Hcap0).
assert (Hc2z : WriterApp.w_cap st2 = 0 -> cap = 0) by (clear - Hcm2 Hcap0; lia).
assert (Hc20 : 0 <= WriterApp.w_cap st2) by (clear - Hcm2 Hcap0; lia).
(* ---- from put #2's return to put #3's call ---- *)
assert (E19 : bv_unsigned (ew (Ereg regs2 X) 19) = o)
  by (rewrite (ew_Ereg_nat regs2 X 19 19%bv eq_refl), R19; exact (wz o Ao64)).
apply (psj_put2_put3 B (Z.of_nat (length bs)) psj_scs0 [] o (Ereg regs2 X)
  (mkst regs2 (Z_to_bv 64 PS_END_RET) mem2 (seg_rom tfibsegs)) STKw ot FPw ly S W (unpoison U mem) md [(0, pos)]
  ly2 S2 U2 W2 md2 k2 Q HS2 HJ2 HARU2 E19).
intros ms' mat' HS' HJ' HARU' MEQ R1' R10' R11' R12'.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) (Ereg regs2 X) _ ms' HS' eq_refl).
set (md2' := with_vm_backing (m_vm_lazy md2) mat' md2) in *.
change (forall x, ms_mem ms' x = mem2 x) in MEQ.
set (memc := ms_mem ms') in *.
set (regsc := ms_regs ms') in *.
pose proof (ARU_AR tfibsegs B ly2 S2 U2 W2 memc md2' HARU') as HAR'.
(* the registers at the call (MEASURED in psj_put3_regs: atoms, x21 = atom 24, x22 = atom 47, x23 = atom 32) *)
assert (C2 : getr regsc 2%bv = Z_to_bv 64 sp1)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 2%bv 2%bv 2 HS' ltac:(vm_compute; reflexivity) eq_refl) R2).
assert (C3 : getr regsc 3%bv = getr regs 3%bv)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 3%bv 3%bv 3 HS' ltac:(vm_compute; reflexivity) eq_refl) R3).
assert (C4 : getr regsc 4%bv = getr regs 4%bv)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 4%bv 4%bv 4 HS' ltac:(vm_compute; reflexivity) eq_refl) R4).
assert (C8 : getr regsc 8%bv = Z_to_bv 64 sp0)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 8%bv 8%bv 8 HS' ltac:(vm_compute; reflexivity) eq_refl) R8).
assert (C9 : getr regsc 9%bv = Z_to_bv 64 sp1)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 9%bv 9%bv 9 HS' ltac:(vm_compute; reflexivity) eq_refl) R9).
assert (C19 : getr regsc 19%bv = Z_to_bv 64 o)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 19%bv 19%bv 19 HS' ltac:(vm_compute; reflexivity) eq_refl)
              R19).
assert (C21 : getr regsc 21%bv = Z_to_bv 64 F)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 21%bv 24%bv 24 HS' ltac:(vm_compute; reflexivity) eq_refl)
              R24).
assert (C22 : getr regsc 22%bv = Z_to_bv 64 (shadow_addr F))
  by exact (fsw_reg_extra (w_H W2) regs2 X _ ms' 22%bv 15 HS' ltac:(vm_compute; reflexivity)).
assert (C23 : getr regsc 23%bv = Z_to_bv 64 SHADOW_OFF)
  by exact (fsw_reg_extra (w_H W2) regs2 X _ ms' 23%bv 0 HS' ltac:(vm_compute; reflexivity)).
assert (C24 : getr regsc 24%bv = Z_to_bv 64 F)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 24%bv 24%bv 24 HS' ltac:(vm_compute; reflexivity) eq_refl)
              R24).
assert (C26 : getr regsc 26%bv = Z_to_bv 64 s)
  by exact (eq_trans (fsw_reg_atom (w_H W2) regs2 X _ ms' 26%bv 26%bv 26 HS' ltac:(vm_compute; reflexivity) eq_refl)
              R26).
assert (Esp : spZ regsc = sp1) by (unfold spZ; rewrite C2; exact (wz sp1 A64)).
assert (Es0 : s0Z regsc = sp0) by (unfold s0Z; rewrite C8; exact (wz sp0 Asp064)).
(* the saved-word region at s0 (the first region of the call-site state) *)
pose proof (st_ok_mem_ok tfibsegs _ _ _ HS') as (_ & OKR & _).
cbn [ss_mem ps_ret_regions ms_mem restrict] in OKR.
pose proof (Forall_inv OKR) as RSV.
assert (U8 : bv_unsigned (ew (Ereg regs2 X) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs2 X 8 8%bv eq_refl), R8; exact (wz sp0 Asp064)).
destruct (ps_saved_words (Ereg regs2 X) (w_H W2) memc sp0 (raZ regs) (s0Z regs) RSV U8
  ltac:(rewrite ps_ew_x; reflexivity) ltac:(rewrite ps_ew_x; reflexivity)
  (u64_range (getr regs 1%bv)) (u64_range (getr regs 8%bv))) as (W8 & W16).
assert (RC : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 X) (mrestrict (w_H W2) memc) sp0) ps_sv_chunks).
{ destruct RSV as (_ & _ & _ & RC). cbn [YP09.r_chunks YP09.r_base base_val] in RC. rewrite U8 in RC. exact RC. }
(* ---- the premises of ps_put_call at the closing quote ---- *)
assert (P_RO : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) memc))
  by exact (ps_aro_pt B W2 mem2 memc MEQ HRO2).
assert (P_sp : spZ regsc = ot + (sp1 - ot)) by (rewrite Esp; ring).
assert (P_ret : YK0s.ret_ok (getr regsc 1%bv)) by (rewrite R1'; vm_compute; reflexivity).
assert (P_ra4 : 4096 <= raZ regsc)
  by (unfold raZ; rewrite R1', (wz PS_CLOSE_RET ltac:(unfold PS_CLOSE_RET; lia)); unfold PS_CLOSE_RET; lia).
assert (P_gp : getr regsc 3 = w64 (as_gp B)) by (rewrite C3; exact Hgp0).
assert (P_tp : getr regsc 4 = w64 (as_tp B)) by (rewrite C4; exact Htp0).
assert (Hkeepc : forall a, sp0 <= a < ot -> ~ (o <= a < o + 32) ->
           mbyte tfibsegs (mrestrict (w_H W2) memc) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha Ho. rewrite (psj_mbyte_pt (w_H W2) mem2 memc a (MEQ _)). exact (proj1 (HKEEP2 a Ha Ho)). }
assert (Hag : forall a, sp0 <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
           aview tfibsegs (w_H W2) (unpoison U2 memc) a = aview tfibsegs (w_H W) (unpoison U mem) a)
  by exact (ps_chain_agree B STKw ot FPw ly S U W mem md [(0, pos)] ly2 S2 U2 W2 memc md2' k2 sp0 o
              HJ' HARU0 HARU' ltac:(unfold STKw; clear - Ajt Asp10; lia) ltac:(clear - Aac Asp10; lia) Hkeepc).
pose proof asan_consts as (AC1 & _ & AC3 & _).
assert (Hhi1 : kHighMemBeg <= sp1) by (rewrite AC3; clear - AC1 Aac; lia).
assert (Hhi0 : kHighMemBeg <= sp0 - 16) by (clear - Hhi1 A16; lia).
assert (W8u : rdword (aview tfibsegs (w_H W2) (unpoison U2 memc)) (sp0 - 8) = Some (raZ regs))
  by exact (ps_rdword_unpoison B ly2 S2 U2 W2 memc md2' (sp0 - 8) (raZ regs) HARU' ltac:(clear - Hhi0; lia)
              ltac:(clear - Asp064; lia) W8).
assert (W16u : rdword (aview tfibsegs (w_H W2) (unpoison U2 memc)) (sp0 - 16) = Some (s0Z regs))
  by exact (ps_rdword_unpoison B ly2 S2 U2 W2 memc md2' (sp0 - 16) (s0Z regs) HARU' Hhi0
              ltac:(clear - Asp064; lia) W16).
assert (P_ch : achain ly2 (aview tfibsegs (w_H W2) (unpoison U2 memc)) (spZ regsc) (s0Z regsc) (ps_ch1 ly regs ch)).
{ rewrite Esp, Es0.
  apply (ps_chain_call B ly S U W regs mem md ch o ly2 W2 (unpoison U2 memc) sp1 (proj1 HPRE) HFPc Etop2);
    [| exact W8u | exact W16u | exact A16].
  intros a Ha Ho. apply Hag; [clear - Ha Htop2 H47s; lia | exact Ho]. }
assert (P_fr : Z.of_nat (length (frames S2)) <= FRL_CRT_CALLEE + 1)
  by (rewrite Efr2; exact (ps_frames_callee (0, pos) (frames S) Hfr)).
assert (P_out : FSH_Fn_writer.wout_ok B tfibsegs ly2 S2 W2 memc o buf2 (WriterApp.w_cap st2)
                  (WriterApp.w_failed st2) (WriterApp.w_text st2))
  by exact (ps_wout_pt B ly2 S2 W2 mem2 memc o buf2 _ _ _ MEQ HOUT2).
assert (P_glob : fs_glob tfibsegs W2 memc (live + WriterApp.w_cap st2 - cap) peak2 (WriterApp.w_cnt st2)
                   (WriterApp.w_fail st2))
  by exact (pske_glob W2 W2 mem2 memc (fun _ => False) _ _ _ _ (ps_agree_pt W2 mem2 memc _ MEQ)
              (fun _ _ Hf => Hf) HGLOB2).
assert (P_top : ot <= ly_top ly2) by (rewrite Etop2; exact Hottop).
assert (P_cho : o = spZ regsc + 8 /\ raZ regsc < alloc_ceiling \/
                spZ regsc + 16 <= o /\ exists ra nfp,
                  rdword (aview tfibsegs (w_H W2) (unpoison U2 memc)) (o - 8) = Some ra /\
                  rdword (aview tfibsegs (w_H W2) (unpoison U2 memc)) (o - 16) = Some nfp /\
                  (ra < 4096 \/ nfp < alloc_ceiling)).
{ apply (psk_chain_o (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W2) (unpoison U2 memc))
           regs regsc o Hcho); [rewrite Esp; exact A16 | | | exact W8u].
  - intros a Ha. apply Hag; [clear - Ha Ao64; lia | clear - Ha; lia].
  - intros a Ha. rewrite (aview_unpoison_out tfibsegs (w_H W2) U2 memc a).
    + apply ps_aview_some. unfold apresent in *. rewrite (MEQ _).
      exact (HPR2 a ltac:(clear - Ha A192 Asp08; lia)).
    + rewrite (wz a ltac:(clear - Ha Asp064 Asp08 Hot47; lia)).
      exact (pske_ush_aru B ly2 S2 U2 W2 memc md2' a HARU' ltac:(right; clear - Ha Hhi0; lia)). }
assert (P_pres : forall a, spZ regsc <= a < ot -> apresent (w_H W2) memc a).
{ rewrite Esp. intros a Ha. unfold apresent in *. rewrite (MEQ _). exact (HPR2 a Ha). }
destruct (ps_quote_src B HIMG ly2 S2 U2 W2 memc md2' buf2 HARU' P_RO) as (P_z & P_src & P_s0n).
assert (P_bok : WriterSpec.bytes_ok [34]) by (constructor; [cbv beta; lia | constructor]).
assert (P_wm : Z.of_nat (length (WriterApp.w_text st2)) + 1 + 1 <= FSH_Fn_writer.WMAX)
  by exact (psg3_wmax failed text cap cnt fail bs Hplain Hwmax).
assert (P_capw : WriterApp.w_cap st2 <= FSH_Fn_writer.WMAX) by exact (proj1 HBK2).
assert (P_live : WriterApp.w_cap st2 <= live + WriterApp.w_cap st2 - cap) by (clear - Hlive; lia).
assert (P_bp : FSH_Fn_writer.wbudget_pre S2 (WriterApp.w_cap st2) (WriterApp.w_cnt st2)
                 (live + WriterApp.w_cap st2 - cap)
                 (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st2) (WriterApp.w_text st2)
                    (WriterApp.w_cap st2) (WriterApp.w_cnt st2) (WriterApp.w_fail st2) []) [34]))
  by exact (psg3_bp S S2 failed text cap cnt fail live bs k2 Hplain Hcap0 Hcnt0 Hbp eq_refl
              (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ'))))))) HBK2).
assert (P_s0r : forall regs', aregs_preserved regsc regs' -> YK11.getr regs' 8%bv = Z_to_bv 64 sp0).
{ intros r' HP. rewrite (psg3_pres regsc r' 8%bv 8 HP ltac:(unfold acallee_saved; lia)
    ltac:(apply bv_eq; reflexivity)). exact C8. }
assert (P_wf : YP09.regions_wf [fs_ret_s0_region (-104) 0 ps_sv_chunks] = true) by (vm_compute; reflexivity).
assert (P_in : Forall (fun c => -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) ps_sv_chunks).
{ rewrite Forall_forall. intros c Hc. unfold ps_sv_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj).
  apply in_seq in Hj. cbn. lia. }
assert (P_cs : forall regs', Forall (YP09.chunk_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W2) memc) sp0)
                               ps_sv_chunks)
  by (intros r'; exact (ps_sv_move regs2 r' X _ sp0 RC)).
assert (P_FP : forall a, inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf2 (WriterApp.w_cap st2)) a ->
     (inFP FPw a /\ exists b n, In (b, n) (ablocks B ly2 S2) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B ly2 S2) a \/
     (inFP FPw a /\ in_img tfibsegs a) \/
     in_frames ly2 [(0, pos)] a)
  by (intros a Ha; exact (psk_fp_rel B ly S ly2 S2 W2 (unpoison U2 memc) md2' buf cap buf2 (WriterApp.w_cap st2)
                            [(0, pos)] a HAR' HBS2 Hblk2 Ha)).
assert (P_FRfp : forall a, (frame_addr ly2 0 pos <= a < frame_addr ly2 0 pos + fs_frame_bytes 0 \/
                            shadow_addr (frame_addr ly2 0 pos) <= a
                              < shadow_addr (frame_addr ly2 0 pos) + fs_frame_bytes 0 / 8) ->
                  ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf2 (WriterApp.w_cap st2)) a)
  by (intros a Ha; exact (pss_fr_off_fp B ly2 S2 W2 (unpoison U2 memc) md2' 0 pos buf2 _ a mem2 o _ _
                            HAR' Hin2 (Z.le_refl 0) HOUT2 Ha)).
(* ---- put #3: the closing quote ---- *)
apply (ps_put_call B HPUT STKw ot FPw [(0, pos)] ly S U U2 W mem md W2 ly2 S2 memc md2' k2 regsc (sp1 - ot)
  (ps_ch1 ly regs ch) pos PS_CLOSE_RET o PS_Q1 1 buf2 (WriterApp.w_cap st2) (WriterApp.w_failed st2)
  (WriterApp.w_text st2) [34] (live + WriterApp.w_cap st2 - cap) peak2 (WriterApp.w_cnt st2) (WriterApp.w_fail st2)
  ot sp0 (-104) 0 ps_sv_chunks X Q
  HJ' HARU' P_RO P_sp Aoff16 Aoff0 Abud P_ret P_ra4 P_gp P_tp P_ch Hheads2 P_fr R10' R11' R12' P_out P_glob HHD2
  ltac:(rewrite Esp; exact Asp1o) Hoot Hot16 P_top P_cho P_pres P_z P_src eq_refl P_bok P_s0n
  ltac:(left; exact Aq1) P_wm P_capw P_live P_bp R1' P_s0r Hal16 Asp0ot Awin104 ltac:(clear; lia) ltac:(clear; lia)
  ltac:(rewrite Esp; exact Awin) (Z.le_refl ot) ltac:(rewrite Esp; exact Asp1ot) P_wf P_in P_cs
  ltac:(rewrite Esp; exact Alo104) Ahi ltac:(left; exact Asp0o) P_FP Hin2 P_FRfp).
intros st3' buf3 U3 ly3 S3 W3 regs3 mem3 md3 Est HUS3 HJ3 HARU3 HP3 HOUT3 HBK3 HBS3 HKEEP3 HPK3 _ HFRK HS3.
apply (KONT ly3 S3 U3 W3 regs3 mem3 md3 buf3).
(* ---- put #3's return, in ps_inv ---- *)
destruct (psg3_fields3 failed text cap cnt fail bs st3' Est) as (Ff3 & Ft3 & Fc3 & Fn3 & Fl3).
set (st3 := ps_st failed text cap cnt fail [[34]; bs; [34]]) in *.
pose proof HJ3 as (_ & LLE3 & _ & _ & _ & Efr3 & _ & _ & _ & _ & _ & _ & _ & HPW3 & _).
destruct LLE3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 0 pos = F) by (unfold F, frame_addr; rewrite EF3; reflexivity).
assert (EFl3 : flag_addr ly3 0 pos = FL) by (unfold FL, flag_addr; rewrite EF3; reflexivity).
assert (G1 : In (0, pos) (frames S3)) by (rewrite Efr3; left; reflexivity).
assert (EK : FSH_Fn_writer.wevk cap st3 = k2 + FSH_Fn_writer.wevk (WriterApp.w_cap st2) st3')
  by (rewrite Est; exact (psg3_wevk3 failed text cap cnt fail bs)).
assert (G4 : ajournal tfibsegs B STKw ot FPw ly S W (unpoison U mem) md [(0, pos)] ly3 S3 W3 (unpoison U3 mem3) md3
               (FSH_Fn_writer.wevk cap st3)) by (rewrite EK; exact HJ3).
(* the registers after the call: callee-saved, so the call site's *)
assert (Q2 : getr regs3 2%bv = Z_to_bv 64 sp1)
  by exact (eq_trans (psg3_pres regsc regs3 2%bv 2 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C2).
assert (Q3 : getr regs3 3%bv = getr regs 3%bv)
  by exact (eq_trans (psg3_pres regsc regs3 3%bv 3 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C3).
assert (Q4 : getr regs3 4%bv = getr regs 4%bv)
  by exact (eq_trans (psg3_pres regsc regs3 4%bv 4 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C4).
assert (Q8 : getr regs3 8%bv = Z_to_bv 64 sp0)
  by exact (eq_trans (psg3_pres regsc regs3 8%bv 8 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C8).
assert (Q9 : getr regs3 9%bv = Z_to_bv 64 sp1)
  by exact (eq_trans (psg3_pres regsc regs3 9%bv 9 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C9).
assert (Q19 : getr regs3 19%bv = Z_to_bv 64 o)
  by exact (eq_trans (psg3_pres regsc regs3 19%bv 19 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C19).
assert (Q21 : getr regs3 21%bv = Z_to_bv 64 F)
  by exact (eq_trans (psg3_pres regsc regs3 21%bv 21 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C21).
assert (Q22 : getr regs3 22%bv = Z_to_bv 64 (shadow_addr F))
  by exact (eq_trans (psg3_pres regsc regs3 22%bv 22 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C22).
assert (Q23 : getr regs3 23%bv = Z_to_bv 64 SHADOW_OFF)
  by exact (eq_trans (psg3_pres regsc regs3 23%bv 23 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C23).
assert (Q24 : getr regs3 24%bv = Z_to_bv 64 F)
  by exact (eq_trans (psg3_pres regsc regs3 24%bv 24 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C24).
assert (Q26 : getr regs3 26%bv = Z_to_bv 64 s)
  by exact (eq_trans (psg3_pres regsc regs3 26%bv 26 HP3 ltac:(unfold acallee_saved; lia)
                        ltac:(apply bv_eq; reflexivity)) C26).
(* the frame's three chunk sets: put keeps the frame, its shadow and [sp1, o) *)
rewrite EFa2 in HFRK. rewrite Esp in HKEEP3.
assert (G19 : YP09.chunk_ok tfibsegs (Ereg regs3 X) (mrestrict (w_H W3) mem3) sp1
                (YP09.mkChunk 80 (CVal 8 (SOff 24 0)))).
{ apply (ps_slot_move (Ereg regs2 X) (Ereg regs3 X) (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) sp1);
    [| | exact H80].
  - rewrite (ew_Ereg_nat regs3 X 24 24%bv eq_refl), (ew_Ereg_nat regs2 X 24 24%bv eq_refl), Q24, R24.
    reflexivity.
  - intros a Ha. rewrite (proj1 (HKEEP3 a ltac:(clear - Ha A192 Asp0ot; lia) ltac:(clear - Ha A192 Asp0o; lia))).
    exact (psj_mbyte_pt (w_H W2) mem2 memc a (MEQ _)). }
assert (G20 : Forall (YP09.chunk_ok tfibsegs (Ereg regs3 X) (mrestrict (w_H W3) mem3) F) ps_hdr_chunks).
{ apply (ps_hdr_move (Ereg regs2 X) (Ereg regs3 X) (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) F);
    [rewrite !ps_ew_x; reflexivity | | exact Hhdr].
  intros a Ha. rewrite (HFRK a ltac:(left; rewrite pss_fb0; exact Ha)).
  exact (psj_mbyte_pt (w_H W2) mem2 memc a (MEQ _)). }
assert (G21 : Forall (YP09.chunk_ok tfibsegs (Ereg regs3 X) (mrestrict (w_H W3) mem3) (shadow_addr F))
                ps_fsh_chunks).
{ apply (ps_fsh_move (Ereg regs2 X) (Ereg regs3 X) (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3)
           (shadow_addr F)); [| exact Hfsh].
  intros a Ha. rewrite (HFRK a ltac:(right; rewrite pss_fb0; exact Ha)).
  exact (psj_mbyte_pt (w_H W2) mem2 memc a (MEQ _)). }
(* the state at the return, in ps_epilogue's env *)
assert (G6 : st_ok tfibsegs (Ereg regs3 X) (ps_epi_ss PS_CLOSE_RET)
               (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 PS_CLOSE_RET) mem3 (seg_rom tfibsegs)))).
{ pose proof (psr_resume_epi B STKw ot sp0 FPw ly S W (unpoison U mem) md [(0, pos)] ly3 S3 U3 W3 mem3 md3
    (k2 + FSH_Fn_writer.wevk (WriterApp.w_cap st2) st3') regs3 regs pos sp1) as PR.
  rewrite EFa3, EFl3 in PR.
  exact (PR HS3 HJ3 HARU3 G1 Q8 Q9 Q21 Q22 Q23 Q24 Ajt A192 Asp0ot A32 G19 G20 G21). }
(* the spec's relations, composed from the entry *)
assert (Hc3m : WriterApp.w_cap st2 <= WriterApp.w_cap st3').
{ rewrite Est. exact (WriterRet.put1_cap (WriterApp.mkW (WriterApp.w_failed st2) (WriterApp.w_text st2)
    (WriterApp.w_cap st2) (WriterApp.w_cnt st2) (WriterApp.w_fail st2) []) [34] Hc20). }
assert (G22 : FSH_Fn_writer.uswap U U3 buf buf3 cap)
  by exact (psm_uswap2_ar tfibsegs B ly2 S2 U2 W2 memc md2' U U3 buf buf2 buf3 cap (WriterApp.w_cap st2)
              HARU' Hb2z Hc2z Hus2 HUS3).
assert (G25 : FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly3 S3) buf buf3 cap (WriterApp.w_cap st3)).
{ rewrite Fc3. exact (psm_bswap2_ar tfibsegs B ly2 S2 W2 (unpoison U2 memc) md2' (ablocks B ly S) (ablocks B ly3 S3)
    buf buf2 buf3 cap (WriterApp.w_cap st2) (WriterApp.w_cap st3') HAR' Hb2z HBS2 HBS3). }
destruct (ps_heads_put B ly2 S2 U2 W2 memc md2' ly3 S3 U3 W3 mem3 md3 o buf2 buf3 (WriterApp.w_cap st2)
            (WriterApp.w_cap st3') (WriterApp.w_failed st3') (WriterApp.w_text st3')
            HARU' Hheads2 Hb2z HHD2 HARU3 HOUT3 HBS3 HUS3) as (G31 & G30).
assert (G32 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3))
  by exact (psk_arodata_ret B STKw ot ly S U W mem md [(0, pos)] ly3 S3 U3 W3 mem3 md3 _ buf cap
              HJ3 HARU0 HARU3 Hblk0 HRO0).
destruct (ps_str_keep B HIMG STKw ot ly S U W mem md [(0, pos)] ly3 S3 U3 W3 mem3 md3 _ buf cap buf3
            (WriterApp.w_cap st3) s bs HARU0 HRO0 HJ3 HARU3 G31 G32 G25 G22 Hblk0 Hcstr Hsrck) as (G27 & G29).
assert (G26 : wkeep tfibsegs W W3 mem mem3 sp0 ot o 32)
  by exact (ps_wkeep_call W W2 W3 mem mem2 memc mem3 sp0 sp1 ot o HKEEP2 MEQ HKEEP3 Asp10).
assert (G33 : forall a, sp1 <= a < ot -> apresent (w_H W3) mem3 a).
{ intros a Ha. apply (ps_apresent_unpoison B ly3 S3 U3 W3 mem3 md3 a HARU3);
    [clear - Ha A64 Hot47; lia | right; clear - Ha Hhi1; lia |].
  apply HPW3. unfold STKw. clear - Ha Ajt. lia. }
assert (G28 : exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st3) /\
                fs_glob tfibsegs W3 mem3 (live + WriterApp.w_cap st3 - cap) peak' (WriterApp.w_cnt st3)
                  (WriterApp.w_fail st3)).
{ destruct HPK3 as (peak3 & Hpk3 & HG3). exists peak3. rewrite Fc3, Fn3, Fl3.
  split; [exact (psg3_peak peak peak2 peak3 live cap _ _ Hc3m Hpk2 Hpk3)|].
  replace (live + WriterApp.w_cap st3' - cap)
    with (live + WriterApp.w_cap st2 - cap + WriterApp.w_cap st3' - WriterApp.w_cap st2) by ring.
  exact HG3. }
assert (G24 : FSH_Fn_writer.wbudget_kept S S3 failed cap cnt (WriterApp.w_failed st3) (WriterApp.w_cap st3)
                (WriterApp.w_cnt st3)).
{ rewrite Ff3, Fc3, Fn3. exact (psm_wbudget_kept2 S S2 S2 S3 failed cap cnt _ _ _ _ _ _ HBK2 (Z.le_refl _) HBK3). }
assert (G23 : FSH_Fn_writer.wout_ok B tfibsegs ly3 S3 W3 mem3 o buf3 (WriterApp.w_cap st3) (WriterApp.w_failed st3)
                (WriterApp.w_text st3)) by (rewrite Fc3, Ff3, Ft3; exact HOUT3).
assert (G30' : WriterApp.w_cap st3 <> 0 -> In (buf3 - HEAD, HEAD) U3) by (rewrite Fc3; exact G30).
unfold ZZpsclose.ps_inv. cbv zeta.
exact (conj G1 (conj Efr3 (conj eq_refl (conj G4 (conj HARU3 (conj G6 (conj eq_refl (conj Q2 (conj Q8 (conj Q9
  (conj Q19 (conj Q21 (conj Q22 (conj Q23 (conj Q24 (conj Q26 (conj Q3 (conj Q4 (conj G19 (conj G20 (conj G21
  (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 (conj G27 (conj G28 (conj G29 (conj G30' (conj G31 (conj G32
  G33)))))))))))))))))))))))))))))))).
Qed.

(* the statement is ps_close's third premise: ps_close takes psg3 as SEG3 *)
Check (fun SEG1 SEG2 SEG4 => ps_close B SEG1 SEG2 psg3 SEG4).

End G3.
