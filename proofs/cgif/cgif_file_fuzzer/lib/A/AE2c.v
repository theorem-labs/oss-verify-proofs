(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q YA0m YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y AE3i AE2l AE2h AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FWR_ENTRY : Z := 0x93808.
Definition FWR_RA1 : Z := 0x93890.
Definition XTRA0 (cval fd wpos : Z) : list Z := [cval; fd; 0; 0; 0; 0; 0; 0; 0; wpos].
Definition fileE_chunks (wend wpos wbase : sv) (mode : Z) : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 24 (CVal 8 (SLit A_stdio_close)); YP09.mkChunk 32 (CVal 8 wend); YP09.mkChunk 40 (CVal 8 wpos);
YP09.mkChunk 48 (CVal 8 (SLit 0)); YP09.mkChunk 56 (CVal 8 wbase); YP09.mkChunk 64 (CVal 8 (SLit A_stdio_read)); YP09.mkChunk 72 (CVal 8 (SLit A_stdio_write));
YP09.mkChunk 80 (CVal 8 (SLit A_stdio_seek)); YP09.mkChunk 88 (CVal 8 (SOff 13 240)); YP09.mkChunk 96 (CVal 8 (SLit 1024));
YP09.mkChunk 104 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0)); YP09.mkChunk 120 (CVal 4 (SOff 33 0)); YP09.mkChunk 124 (CVal 4 (SLit 0));
YP09.mkChunk 128 (CVal 8 (SLit 0)); YP09.mkChunk 136 (CVal 4 (SLit mode)); YP09.mkChunk 140 (CVal 4 (SLit 4294967295)); YP09.mkChunk 144 (CVal 4 (SLit 4294967295));
YP09.mkChunk 152 (CVal 8 (SLit 0)); YP09.mkChunk 160 (CVal 8 (SLit 0)); YP09.mkChunk 168 (CVal 8 (SLit 0)); YP09.mkChunk 176 (CVal 8 (SLit 0));
YP09.mkChunk 184 (CVal 8 (SLit 0)); YP09.mkChunk 192 (CVal 8 (SLit 0)); YP09.mkChunk 200 (CVal 8 (SLit 0)); YP09.mkChunk 208 (CVal 8 (SLit 0));
YP09.mkChunk 216 (CVal 8 (SLit 0)); YP09.mkChunk 224 (CVal 8 (SLit 0))].
Definition fileEB : YP09.region := YP09.mkRegion (Some 13%nat) 0 232 0 232 (fileE_chunks (SOff 13 1264) (SOff 41 0) (SOff 13 240) 4294967295).
Definition fileEF : YP09.region := YP09.mkRegion (Some 13%nat) 0 232 0 232 (fileE_chunks (SLit 0) (SLit 0) (SLit 0) 0).
Definition stkE : YP09.region := YP09.mkRegion (Some 2%nat) (- FWR_STK) 0 (- FWR_STK) 0 [].
Definition factsE : list (nat * afact) :=
[(2%nat, mkAF (2^43 + 128) (2^47) 4); (13%nat, mkAF 4096 (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 1 (2^30) 0);
(41%nat, mkAF 4096 (2^47) 0); (33%nat, mkAF 0 (2^31-1) 0)].
Definition regsE : list sv := sr_set sr_atoms 11%bv (SLit 1).
Definition ssEB : sstate := mkSS FWR_ENTRY regsE ([stkE; fileEB] ++ canR) None (mkFacts factsE [] []).
Definition ssEF : sstate := mkSS FWR_ENTRY regsE ([stkE; fileEF] ++ canR) None (mkFacts factsE [] []).
Definition eEB : sstate := Eval vm_compute in fst (RUN ssEB).
Definition eEF : sstate := Eval vm_compute in fst (RUN ssEF).
Definition coreregs (wp x11 : sv) : list (Z * sv) :=
[(2, SOff 2 (-128)); (3, SOff 3 0); (4, SOff 4 0); (8, SOff 13 0); (9, SOff 12 0); (10, wp); (11, x11); (18, SOff 10 0);
(22, SOff 22 0); (23, SOff 23 0); (24, SOff 24 0); (25, SOff 25 0); (26, SOff 26 0); (27, SOff 27 0)].
Definition corestk : list (Z * sv) :=
[(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-32, SOff 18 0); (-40, SOff 19 0); (-48, SOff 20 0); (-56, SOff 21 0);
(-72, SLit FWR_RA1); (-80, SOff 12 0); (-88, SLit 1); (-96, SMd M_MUL (SOff 12 0) (SLit 1)); (-104, SOff 13 0); (-112, SOff 20 0); (-120, SOff 21 0)].
Definition hdr13 (wp md : sv) : list (Z * N * sv) :=
[(0, 4%N, SLit 4); (8, 8%N, SLit 0); (16, 8%N, SLit 0); (24, 8%N, SLit A_stdio_close); (32, 8%N, SOff 13 1264); (40, 8%N, wp); (48, 8%N, SLit 0); (56, 8%N, SOff 13 240);
(64, 8%N, SLit A_stdio_read); (72, 8%N, SLit A_stdio_write); (80, 8%N, SLit A_stdio_seek); (88, 8%N, SOff 13 240); (96, 8%N, SLit 1024); (104, 8%N, SLit 0); (112, 8%N, SLit 0);
(120, 4%N, SOff 33 0); (124, 4%N, SLit 0); (128, 8%N, SLit 0); (136, 4%N, md); (140, 4%N, SLit 4294967295); (144, 4%N, SLit 4294967295);
(152, 8%N, SLit 0); (160, 8%N, SLit 0); (168, 8%N, SLit 0); (176, 8%N, SLit 0); (184, 8%N, SLit 0); (192, 8%N, SLit 0); (200, 8%N, SLit 0); (208, 8%N, SLit 0); (216, 8%N, SLit 0); (224, 8%N, SLit 0)].
Definition shapeE (e : sstate) (wp x11 md : sv) : bool :=
(ss_pc e =? FWX_BR)
&& forallb (fun p => reg_is e (fst p) (snd p)) (coreregs wp x11)
&& forallb (fun p => has_chunk e 0 (fst p) 8 (snd p)) corestk
&& forallb (fun c => has_chunk e 1 (fst (fst c)) (snd (fst c)) (snd c)) (hdr13 wp md)
&& match ss_resv e with None => true | _ => false end
&& match f_conds (ss_facts e) with [] => true | _ => false end
&& match ss_mem e with
| [r0; r1; r2; r3] => skel_is r0 (Some 2%nat) (- FWR_STK) 0 (- FWR_STK) 0 && skel_is r1 (Some 13%nat) 0 232 0 232
&& skel_is r2 None A_GOT_canary (A_GOT_canary + 8) 0 0 && skel_is r3 None A_canary (A_canary + 8) 0 0
| _ => false end.
Lemma runB_eq : RUN ssEB = (eEB, RS_stopped (SR_branch BC_GEU (SAlu ALU_ADD (SOff 13 1264) (SMd M_MUL (SOff 41 0) (SLit (-1)))) (SOff 12 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma runF_eq : RUN ssEF = (eEF, RS_stopped (SR_branch BC_GEU (SLit 1024) (SOff 12 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma shapeB_ok : shapeE eEB (SOff 41 0) (SAlu ALU_ADD (SOff 13 1264) (SMd M_MUL (SOff 41 0) (SLit (-1)))) (SLit 4294967295) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma shapeF_ok : shapeE eEF (SOff 13 240) (SLit 1024) (SLit 18446744073709551615) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma windowsE : forall fr, windows ([stkE; fr] ++ canR) = [(Some 2%nat, - FWR_STK, 0); (YP09.r_base fr, YP09.r_wlo fr, YP09.r_whi fr); (None, 0, 0); (None, 0, 0)].
Proof. intros fr. reflexivity. Qed.
Lemma shapeE_sound : forall e wp x11 md, shapeE e wp x11 md = true ->
ss_pc e = FWX_BR /\ (forall r v, In (r, v) (coreregs wp x11) -> reg_is e r v = true) /\
(forall o v, In (o, v) corestk -> has_chunk e 0 o 8 v = true) /\
(forall o nn v, In (o, nn, v) (hdr13 wp md) -> has_chunk e 1 o nn v = true) /\
ss_resv e = None /\ f_conds (ss_facts e) = [] /\
exists r0 r1 r2 r3, ss_mem e = [r0; r1; r2; r3] /\
skel_is r0 (Some 2%nat) (- FWR_STK) 0 (- FWR_STK) 0 = true /\ skel_is r1 (Some 13%nat) 0 232 0 232 = true /\
skel_is r2 None A_GOT_canary (A_GOT_canary + 8) 0 0 = true /\ skel_is r3 None A_canary (A_canary + 8) 0 0 = true.
Proof.
intros e wp x11 md Hs. unfold shapeE in Hs.
apply andb_prop in Hs as [Hs Hm]. apply andb_prop in Hs as [Hs Hc]. apply andb_prop in Hs as [Hs Hv]. apply andb_prop in Hs as [Hs Hh].
apply andb_prop in Hs as [Hs Hk]. apply andb_prop in Hs as [Hpc Hr]. apply Z.eqb_eq in Hpc.
split; [exact Hpc|].
split; [intros r v Hin; rewrite forallb_forall in Hr; exact (Hr (r, v) Hin)|].
split; [intros o v Hin; rewrite forallb_forall in Hk; exact (Hk (o, v) Hin)|].
split; [intros o nn v Hin; rewrite forallb_forall in Hh; exact (Hh (o, nn, v) Hin)|].
split; [destruct (ss_resv e); [discriminate Hv | reflexivity]|].
split; [destruct (f_conds (ss_facts e)); [reflexivity | discriminate Hc]|].
destruct (ss_mem e) as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]]; try discriminate Hm.
apply andb_prop in Hm as [Hm K3]. apply andb_prop in Hm as [Hm K2]. apply andb_prop in Hm as [K0 K1].
exists r0, r1, r2, r3. repeat split; assumption.
Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (f fd n src cval : Z) (P bs Wb : list Z).
Let sp0 : Z := spZ regs0.
Let H := w_H W.
Let m0 := mrestrict H mem0.
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Hra0 : YK0s.ret_ok (getr regs0 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FWR_STK <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis HpresE : forall a, sp0 - FWR_STK <= a < sp0 -> apresent H mem0 a.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Htp : getr regs0 4 = w64 (as_tp B).
Hypothesis A0 : getr regs0 10 = w64 src.
Hypothesis A1 : getr regs0 11 = w64 1.
Hypothesis A2 : getr regs0 12 = w64 n.
Hypothesis A3 : getr regs0 13 = w64 f.
Hypothesis HFILE : file_at tfibsegs tfib_K m0 f fd P.
Hypothesis Hf0 : 4096 <= f.
Hypothesis Hfhi : f + FILE_BLOCK <= 2 ^ 47.
Hypothesis Hfal : f mod 16 = 0.
Hypothesis Hfd : 0 <= fd < 2 ^ 31.
Hypothesis HBLK : forall a, f <= a < f + FILE_BLOCK -> apresent H mem0 a /\ ~ aowned B ly S a.
Hypothesis HBstk : f + FILE_BLOCK <= sp0 - FWR_STK \/ sp0 <= f.
Hypothesis HBimg : f + FILE_BLOCK <= TFIB_IMG_LO \/ TFIB_IMG_END <= f.
Hypothesis HBam : amem_range f FILE_BLOCK.
Hypothesis HBra : range_addressable (aview tfibsegs H mem0) SHADOW_OFF (f + 240) 1024.
Hypothesis HBhull : shadow_hull_vis (aview tfibsegs H mem0) (f + 240) 1024.
Hypothesis HSRC : garr8 tfibsegs m0 src bs.
Hypothesis Hn : n = Z.of_nat (length bs).
Hypothesis Hn1 : 1 <= n <= 2 ^ 30.
Hypothesis Hsrc0 : 0 <= src.
Hypothesis Hsrchi : src + n <= 2 ^ 47.
Hypothesis HSf : src + n <= f \/ f + FILE_BLOCK <= src.
Hypothesis HSstk : src + n <= sp0 - FWR_STK \/ sp0 <= src.
Hypothesis HSam : amem_range src n.
Hypothesis HSra : range_addressable (aview tfibsegs H mem0) SHADOW_OFF src n.
Hypothesis HShull : shadow_hull_vis (aview tfibsegs H mem0) src n.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis HfdL : fd_lookup (m_fds md0) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb)))).
Hypothesis HfsL : Fs.fs_lookup (m_fs md0) sink_path = Some (YE00.bytes Wb).
Hypothesis HSmax : Z.of_nat (length Wb) + Z.of_nat (length P) + n <= SINK_MAX.
Definition EPOST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' (Wb' P' : list Z),
c' = cfg_at tfibsegs (raZ regs0) regs' mem' md' /\ AR tfibsegs B ly S W mem' md' /\
aregs_preserved regs0 regs' /\ getr regs' 10 = w64 n /\
m_vmmaps md' = m_vmmaps md0 /\ m_vm_lazy md' = m_vm_lazy md0 /\ os_kept md0 md' /\
Wb' ++ P' = Wb ++ P ++ bs /\ Z.of_nat (length P') <= 1024 /\
hdr_is (mrestrict H mem') f (f + 240 + Z.of_nat (length P')) fd /\
garr8 tfibsegs (mrestrict H mem') (f + 240) P' /\
Fs.fs_lookup (m_fs md') sink_path = Some (YE00.bytes Wb') /\
(Fs.fs_sorted (m_fs md0) = true -> Fs.fs_sorted (m_fs md') = true) /\
m_fds md' = (if (length Wb' =? length Wb)%nat then m_fds md0 else fd_insert (m_fds md0) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb'))))) /\
(forall q, q <> sink_path -> Fs.fs_lookup (m_fs md') q = Fs.fs_lookup (m_fs md0) q) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + FILE_BLOCK) -> ~ (sp0 - FWR_STK <= a < sp0) -> aview tfibsegs H mem' a = aview tfibsegs H mem0 a) /\
(forall a, apresent H mem0 a -> apresent H mem' a).
Let wpos : Z := f + 240 + Z.of_nat (length P).
Let E0 : env := AE2y.Env regs0 (XTRA0 cval fd wpos).
Let ms0 : machine_state := mkst regs0 (Z_to_bv 64 FWR_ENTRY) mem0 (seg_rom tfibsegs).
Lemma facts0E : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ FILE_BLOCK = 1264 /\ FWR_STK = 4224 /\ 0 <= Z.of_nat (length P) <= 1024 /\ (ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 4224 <= sp0).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (HPL : Z.of_nat (length P) <= 1024).
{ destruct HFILE as [_ [(-> & _) | (_ & _ & _ & _ & _ & HL)]]; [cbn; lia | unfold FILE_BUFSIZ in HL; exact HL]. }
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : FWR_STK = 4224) by reflexivity. rewrite FB, FS in *. subst sp0.
repeat split; lia.
Qed.
Lemma E0_facts :
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs0 r) /\
(forall j z, nth_error (XTRA0 cval fd wpos) j = Some z -> ew E0 (32 + j) = Z_to_bv 64 z) /\
bv_unsigned (ew E0 2) = sp0 /\ ew E0 13 = Z_to_bv 64 f /\ ew E0 12 = Z_to_bv 64 n /\ ew E0 10 = Z_to_bv 64 src /\ ew E0 11 = Z_to_bv 64 1 /\
ew E0 32 = Z_to_bv 64 cval /\ ew E0 33 = Z_to_bv 64 fd /\ ew E0 41 = Z_to_bv 64 wpos /\
bv_unsigned (ew E0 13) = f /\ bv_unsigned (ew E0 41) = wpos /\ bv_unsigned (ew E0 12) = n /\ bv_unsigned (ew E0 10) = src.
Proof.
pose proof facts0E as (Hsp & FB & FS & HP0 & Lhi).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs0 r) by (intros; apply AE2y.Env_reg; assumption).
assert (EEx : forall j z, nth_error (XTRA0 cval fd wpos) j = Some z -> ew E0 (32 + j) = Z_to_bv 64 z) by (intros j z Hj; exact (AE2y.Env_x regs0 _ j z Hj)).
split; [exact EEreg|]. split; [exact EEx|].
split; [rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity|].
split; [rewrite (EEreg 13%nat 13%bv eq_refl); exact A3|]. split; [rewrite (EEreg 12%nat 12%bv eq_refl); exact A2|].
split; [rewrite (EEreg 10%nat 10%bv eq_refl); exact A0|]. split; [rewrite (EEreg 11%nat 11%bv eq_refl); exact A1|].
split; [exact (EEx 0%nat cval eq_refl)|]. split; [exact (EEx 1%nat fd eq_refl)|]. split; [exact (EEx 9%nat wpos eq_refl)|].
split; [rewrite (EEreg 13%nat 13%bv eq_refl), A3; apply unsigned_lit_small; lia|].
split; [change (ew E0 41) with (ew E0 (32 + 9)); rewrite (EEx 9%nat wpos eq_refl); apply unsigned_lit_small; subst wpos; lia|].
split; [rewrite (EEreg 12%nat 12%bv eq_refl), A2; apply unsigned_lit_small; lia|].
rewrite (EEreg 10%nat 10%bv eq_refl), A0; apply unsigned_lit_small; lia.
Qed.
Lemma entry_st_ok : forall fr,
(fr = fileEB /\ True /\
(val_mem tfibsegs m0 (f + 32) 8 (f + 1264) /\ val_mem tfibsegs m0 (f + 40) 8 wpos /\ val_mem tfibsegs m0 (f + 56) 8 (f + 240) /\ val_mem tfibsegs m0 (f + 136) 4 4294967295))
\/ (fr = fileEF /\ P = [] /\
(val_mem tfibsegs m0 (f + 32) 8 0 /\ val_mem tfibsegs m0 (f + 40) 8 0 /\ val_mem tfibsegs m0 (f + 56) 8 0 /\ val_mem tfibsegs m0 (f + 136) 4 0)) ->
st_ok tfibsegs E0 (mkSS FWR_ENTRY regsE ([stkE; fr] ++ canR) None (mkFacts factsE [] [])) (restrict H ms0).
Proof.
intros fr Hfr.
pose proof facts0E as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof E0_facts as (EEreg & EEx & EE2 & EE13 & EE12 & EE10 & EE11 & EE32 & EE33 & EE41 & EE13u & EE41u & EE12u & EE10u).
destruct HFILE as [HST HWIN].
subst ms0. rewrite restrict_mkst_fx. unfold E0, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs0 (map (Z_to_bv 64) (XTRA0 cval fd wpos))) with E0.
-
intros r. unfold regsE. destruct (bv_eq_dec _ r 11%bv) as [->|Hne].
+ rewrite sr_get_set_same by reflexivity. cbn [sv_denot]. exact A1.
+ rewrite sr_get_set_other by (intros E; apply Hne; exact E). apply regs_ok_Ereg.
- destruct Hfr as [(-> & _) | (-> & _)]; vm_compute; reflexivity.
- apply Forall_cons.
{
unfold stkE, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EE2. unfold FWR_STK.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AE2y.apresent_writable; apply HpresE; unfold sp0 in *; rewrite FS; lia | apply Forall_nil]. }
apply Forall_cons.
{
assert (HC : forall o nn v, In (o, nn, v) [(0, 4%N, 4); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, A_stdio_close); (48, 8%N, 0); (64, 8%N, A_stdio_read); (72, 8%N, A_stdio_write);
(80, 8%N, A_stdio_seek); (88, 8%N, f + 240); (96, 8%N, 1024); (104, 8%N, 0); (112, 8%N, 0); (120, 4%N, fd); (124, 4%N, 0); (128, 8%N, 0);
(140, 4%N, 4294967295); (144, 4%N, 4294967295); (152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0);
(200, 8%N, 0); (208, 8%N, 0); (216, 8%N, 0); (224, 8%N, 0)] ->
val_mem tfibsegs m0 (f + o) (N.to_nat nn) v).
{ intros o nn v Hin. unfold file_static in HST. unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1 in HST. cbn [ak_close ak_read ak_write ak_seek tfib_K] in HST.
repeat match type of HST with _ /\ _ => let X := fresh "C" in destruct HST as [X HST] end.
cbn [In] in Hin.
repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-; cbn [N.to_nat]; assumption|]). destruct Hin. }
assert (CK : forall o nn e v, sv_denot E0 e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 -> val_mem tfibsegs m0 (f + o) (N.to_nat nn) v ->
YP09.chunk_ok tfibsegs E0 m0 f (YP09.mkChunk o (CVal nn e))).
{ intros o nn e v He Hv Hn8 Hval. exact (chunk_ok_val tfibsegs E0 m0 f o nn e v He Hv Hn8 Hval). }
destruct Hfr as [(-> & _ & (W32 & W40 & W56 & W136)) | (-> & _ & (W32 & W40 & W56 & W136))];
unfold fileEB, fileEF, region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite EE13u;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply AE2y.apresent_writable; apply (proj1 (HBLK (f + o) ltac:(lia)))|]);
unfold fileE_chunks; subst m0.
+ repeat (apply Forall_cons; [ eapply CK;
[cbn [sv_denot]; rewrite ?EE13, ?EE41, ?EE33, ?Z.add_0_r, ?unsigned_lit_small; [reflexivity | lia ..]
| unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; subst wpos; cbn; lia | cbn; lia
| first [exact W32 | exact W40 | exact W56 | exact W136 | (apply HC; cbn [In]; repeat (first [left; reflexivity | right]))] ] |]).
apply Forall_nil.
+ repeat (apply Forall_cons; [ eapply CK;
[cbn [sv_denot]; rewrite ?EE13, ?EE41, ?EE33, ?Z.add_0_r, ?unsigned_lit_small; [reflexivity | lia ..]
| unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; subst wpos; cbn; lia | cbn; lia
| first [exact W32 | exact W40 | exact W56 | exact W136 | (apply HC; cbn [In]; repeat (first [left; reflexivity | right]))] ] |]).
apply Forall_nil. }
unfold canR. subst m0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_canary, A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 _ 0 0x9ec38 8 (SLit 0x5f8fd0) 0x5f8fd0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan1]. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 _ 0 0x5f8fd0 8 (SOff 32 0) cval); [cbn [sv_denot]; rewrite EE32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan2]. }
- apply pairwise_disjoint_of_extents.
assert (Efr : extent_of_region E0 fr = (f + 0, f + 232)).
{ destruct Hfr as [(-> & _) | (-> & _)]; unfold fileEB, fileEF, extent_of_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite EE13u; reflexivity. }
change (map (extent_of_region E0) ([stkE; fr] ++ canR)) with (extent_of_region E0 stkE :: extent_of_region E0 fr :: map (extent_of_region E0) canR).
rewrite Efr. unfold stkE, canR, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N].
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite EE2. unfold A_GOT_canary, A_canary, FWR_STK.
unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsE]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE13, EE10, EE12, EE41, EE33, !unsigned_lit_small by (subst wpos; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. subst wpos. repeat split; lia.
Qed.
Lemma core_tail : forall e wp x11 mdv ms1 mat1,
shapeE e wp x11 mdv = true ->
st_ok tfibsegs E0 e (restrict H ms1) ->
(forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms1 z = mem0 z) ->
U E0 wp = wpos -> U E0 x11 = f + 1264 - wpos ->
(forall m b, YP09.chunk_ok tfibsegs E0 m b (YP09.mkChunk 136 (CVal 4 mdv)) -> val_mem tfibsegs m (b + 136) 4 4294967295) ->
garr8 tfibsegs m0 (f + 240) P ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) EPOST.
Proof.
intros e wp x11 mdv ms1 mat1 Hshape HS1 MEQ Uwp Ux11 MDV HP.
pose proof facts0E as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof E0_facts as (EEreg & EEx & EE2 & EE13 & EE12 & EE10 & EE11 & EE32 & EE33 & EE41 & EE13u & EE41u & EE12u & EE10u).
destruct (shapeE_sound e wp x11 mdv Hshape) as (Hpc & RGs & CS & CH & Hresv & Hconds & r0 & r1 & r2 & r3 & Hmem & K0 & K1 & K2 & K3).
apply skel_is_sound in K0 as (W0a & RL0 & RH0 & W0b & W0c). apply skel_is_sound in K1 as (W1a & RL1 & RH1 & W1b & W1c).
rewrite ?FS in W0b, RL0.
assert (Hwr : 0 <= wpos /\ wpos + 0 <= f + 1264 /\ f + 240 <= wpos) by (subst wpos; lia).
assert (RD : forall (r : bv 5) v, reg_is e (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E0 e ms1 r HS1). }
set (regs1 := ms_regs ms1) in *.
pose proof (st_ok_restrict_mkst tfibsegs H E0 _ _ HS1 Hresv) as Hms1. rewrite Hpc in Hms1. fold regs1 in Hms1.
set (md1 := with_vm_backing (m_vm_lazy md0) mat1 md0).
assert (MF1 : same_but_materialized md0 md1) by (subst md1; apply with_vm_backing_same).
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (bv_unsigned r, SOff i 0) (coreregs wp x11) -> getr regs1 r = getr regs0 (Z_to_bv 5 (Z.of_nat i))).
{ intros r i Hi Hin. rewrite (RD r (SOff i 0) (RGs _ _ Hin)). cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. rewrite Hi, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q2 : getr regs1 2 = w64 (sp0 - 128)).
{ rewrite (RD 2%bv (SOff 2 (-128)) (RGs 2 _ ltac:(INL))). cbn [sv_denot]. rewrite EE2. reflexivity. }
assert (Q3 : getr regs1 3 = getr regs0 3) by exact (RK 3%bv 3%nat eq_refl ltac:(INL)).
assert (Q4 : getr regs1 4 = getr regs0 4) by exact (RK 4%bv 4%nat eq_refl ltac:(INL)).
assert (Q8 : getr regs1 8 = w64 f) by (rewrite (RD 8%bv (SOff 13 0) (RGs 8 _ ltac:(INL))); cbn [sv_denot]; rewrite EE13, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q9 : getr regs1 9 = w64 n) by (rewrite (RD 9%bv (SOff 12 0) (RGs 9 _ ltac:(INL))); cbn [sv_denot]; rewrite EE12, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q18 : getr regs1 18 = w64 src) by (rewrite (RD 18%bv (SOff 10 0) (RGs 18 _ ltac:(INL))); cbn [sv_denot]; rewrite EE10, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q10 : getr regs1 10 = w64 wpos) by (rewrite (RD 10%bv wp (RGs 10 _ ltac:(INL))); rewrite denot_lit_U, Uwp; reflexivity).
assert (Q11 : getr regs1 11 = w64 (f + 1264 - wpos)) by (rewrite (RD 11%bv x11 (RGs 11 _ ltac:(INL))); rewrite denot_lit_U, Ux11; reflexivity).
assert (QK : forall r, In r KEPTR -> getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
{ intros r Hr. unfold KEPTR in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [exact Q3 | exact Q4 | exact (RK 22%bv 22%nat eq_refl ltac:(INL)) | exact (RK 23%bv 23%nat eq_refl ltac:(INL))
| exact (RK 24%bv 24%nat eq_refl ltac:(INL)) | exact (RK 25%bv 25%nat eq_refl ltac:(INL))
| exact (RK 26%bv 26%nat eq_refl ltac:(INL)) | exact (RK 27%bv 27%nat eq_refl ltac:(INL))] |]).
destruct Hr. }
pose proof (st_ok_mem_ok tfibsegs E0 e _ HS1) as Hmemok. cbn [ms_mem restrict] in Hmemok.
pose proof Hmemok as (_ & Hrs & _).
assert (CK0 : forall o v z, In (o, v) corestk -> sv_denot E0 v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + o) 8 z).
{ intros o v z Hin Hd Hz. pose proof (CS o v Hin) as Hc. unfold has_chunk in Hc. rewrite Hmem in Hc. cbn [nth_error] in Hc.
apply existsb_exists in Hc as (c & Hcin & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (proj1 (Forall_forall _ _) Hrs r0 ltac:(rewrite Hmem; left; reflexivity)) as (_ & _ & _ & Hcs). rewrite W0a in Hcs. cbn [base_val] in Hcs. rewrite EE2 in Hcs.
exact (val_of_chunk_ok tfibsegs E0 _ _ o 8 v z (proj1 (Forall_forall _ _) Hcs _ Hcin) Hd Hz ltac:(cbn; lia)). }
assert (U0 : forall r : bv 5, 0 <= bv_unsigned (getr regs0 r) < 2 ^ 64) by (intros r; pose proof (u64_range (getr regs0 r)); lia).
assert (CKreg : forall o i (r : bv 5), Z.of_nat i = bv_unsigned r -> In (o, SOff i 0) corestk -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + o) 8 (bv_unsigned (getr regs0 r))).
{ intros o i r Hi Hin. apply (CK0 o (SOff i 0) _ Hin); [|apply U0]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (HF0' : forall j rz off, nth_error SAVED0 j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 rz)))).
{ intros j rz off Hj. unfold SAVED0 in Hj.
destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn in Hj; [injection Hj as <- <- .. | destruct j; discriminate Hj].
- exact (CKreg (-8) 1%nat 1%bv eq_refl ltac:(INL)).
- exact (CKreg (-16) 8%nat 8%bv eq_refl ltac:(INL)).
- exact (CKreg (-24) 9%nat 9%bv eq_refl ltac:(INL)).
- exact (CKreg (-32) 18%nat 18%bv eq_refl ltac:(INL)).
- exact (CKreg (-40) 19%nat 19%bv eq_refl ltac:(INL)).
- exact (CKreg (-48) 20%nat 20%bv eq_refl ltac:(INL)).
- exact (CKreg (-56) 21%nat 21%bv eq_refl ltac:(INL)). }
assert (HF1' : val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 72) 8 0x93890 /\ val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 80) 8 n /\
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 88) 8 1 /\ val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 96) 8 n /\
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 104) 8 f /\ val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 112) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 - 120) 8 (bv_unsigned (getr regs0 21))).
{ split; [exact (CK0 (-72) (SLit FWR_RA1) 0x93890 ltac:(INL) eq_refl ltac:(lia))|].
split; [apply (CK0 (-80) (SOff 12 0) _ ltac:(INL)); [cbn [sv_denot]; rewrite EE12, Z.add_0_r, unsigned_lit_small by lia; reflexivity | lia]|].
split; [exact (CK0 (-88) (SLit 1) 1 ltac:(INL) eq_refl ltac:(lia))|].
split; [apply (CK0 (-96) (SMd M_MUL (SOff 12 0) (SLit 1)) _ ltac:(INL)); [| lia]; rewrite denot_lit_U, U_SMd, (U_atom E0 12 n EE12), U_lit by lia;
unfold zcanon, M64; cbn [zmd_raw]; rewrite Z.mul_1_r, Z.mod_small by lia; reflexivity|].
split; [apply (CK0 (-104) (SOff 13 0) _ ltac:(INL)); [cbn [sv_denot]; rewrite EE13, Z.add_0_r, unsigned_lit_small by lia; reflexivity | lia]|].
split; [exact (CKreg (-112) 20%nat 20%bv eq_refl ltac:(INL)) | exact (CKreg (-120) 21%nat 21%bv eq_refl ltac:(INL))]. }
assert (HHDR1 : hdr_is (mrestrict H (ms_mem ms1)) f wpos fd).
{ unfold hdr_is. apply Forall_forall. intros [[o nn] v] Hin.
assert (HX : forall sv, In (o, nn, sv) (hdr13 wp mdv) ->
(sv = mdv /\ v = 4294967295 /\ o = 136 /\ nn = 4%N) \/ (sv_denot E0 sv = Z_to_bv 64 v /\ 0 <= v < 2 ^ (8 * Z.of_N nn) /\ Z.of_N nn <= 8) ->
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (f + o) (N.to_nat nn) v).
{ intros sv Hsv Hd. pose proof (CH o nn sv Hsv) as Hc. unfold has_chunk in Hc. rewrite Hmem in Hc. cbn [nth_error] in Hc.
apply existsb_exists in Hc as (c & Hcin & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (proj1 (Forall_forall _ _) Hrs r1 ltac:(rewrite Hmem; right; left; reflexivity)) as (_ & _ & _ & Hcs). rewrite W1a in Hcs. cbn [base_val] in Hcs. rewrite EE13u in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as HCK.
destruct Hd as [(-> & -> & -> & ->) | (Hd & Hr & Hn8)]; [exact (MDV _ _ HCK) | exact (val_of_chunk_ok tfibsegs E0 _ _ o nn sv v HCK Hd Hr Hn8)]. }
unfold hdr_cells in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-;
eapply HX; [unfold hdr13; cbn [In]; repeat (first [left; reflexivity | right])
| first [ (left; repeat split; reflexivity)
| (right; split; [ first [ rewrite denot_lit_U, Uwp; reflexivity
| cbn [sv_denot]; rewrite ?EE33, ?EE13, ?Z.add_0_r; try reflexivity; rewrite unsigned_lit_small by lia; reflexivity ]
| split; [unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; cbn; lia | cbn; lia] ]) ] ] |]).
destruct Hin. }
assert (PRS1 : forall a, sp0 - 4224 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E0 e ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PRSh : forall a, f <= a < f + 232 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E0 e ms1 1 r1 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite W1a, W1b, W1c. cbn [base_val]. rewrite EE13u. lia. }
destruct (frame_AR B LAWS ly S W regs0 mem0 md0 f n src P bs Wb HAR Hslo Hshi HpresE Hf0 Hfhi HBLK HBstk HBimg HBam Hn1 Hsrchi HSf HSstk
mem0 (ms_mem ms1) md0 md1 4224 HAR ltac:(lia) MEQ PRS1 PRSh MF1) as (AV1 & PM1 & HAR1).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 4224 <= a < sp0) -> ~ (f <= a < f + 232) -> mbyte tfibsegs (mrestrict H (ms_mem ms1)) a = mbyte tfibsegs m0 a).
{ intros a Hr H1 H2. subst m0. apply AE2y.mbyte_of_aview. exact (AV1 a Hr H1 H2). }
assert (HP1 : garr8 tfibsegs (mrestrict H (ms_mem ms1)) (f + 240) P).
{ eapply garr8_frame; [exact HP|]. intros a Ha. apply MB1; [lia | rewrite FS in HBstk; lia | lia]. }
assert (HSRC1 : garr8 tfibsegs (mrestrict H (ms_mem ms1)) src bs).
{ eapply garr8_frame; [exact HSRC|]. intros a Ha. apply MB1; [lia | rewrite FS in HSstk; lia | lia]. }
assert (Hcan1' : val_mem tfibsegs (mrestrict H (ms_mem ms1)) A_GOT_canary 8 A_canary).
{ eapply val_mem_frame; [|exact Hcan1]. intros x Hx. unfold A_GOT_canary in Hx. cbn in Hx. apply MB1; [lia | lia | unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg; lia]. }
assert (Hcan2' : val_mem tfibsegs (mrestrict H (ms_mem ms1)) A_canary 8 cval).
{ eapply val_mem_frame; [|exact Hcan2]. intros x Hx. unfold A_canary in Hx. cbn in Hx. apply MB1; [lia | lia | unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg; lia]. }
pose proof (same_but_materialized_frame md0 md1 MF1) as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & Ffds & _ & _ & Ffs & _).
assert (AVband : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs H (ms_mem ms1) s = aview tfibsegs H mem0 s).
{ intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. apply AV1; [lia | lia |].
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HBam. lia. }
assert (RAX : forall a len, 0 <= a -> a + len <= kHighMemEnd -> range_addressable (aview tfibsegs H mem0) SHADOW_OFF a len ->
range_addressable (aview tfibsegs H (ms_mem ms1)) SHADOW_OFF a len).
{ intros a len Ha Hl HR. eapply range_addressable_agree; [|exact HR]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
apply AVband. apply AE2y.shadow_addr_bounds. lia. }
assert (HVX : forall a len, 0 <= a -> 1 <= len -> a + len <= kHighMemEnd -> shadow_hull_vis (aview tfibsegs H mem0) a len ->
shadow_hull_vis (aview tfibsegs H (ms_mem ms1)) a len).
{ intros a len Ha Hl1 Hl HVS s Hs. rewrite AVband; [exact (HVS s Hs)|].
pose proof (AE2y.shadow_addr_bounds a ltac:(lia)) as [B1 B2]. pose proof (AE2y.shadow_addr_bounds (a + len - 1) ltac:(lia)) as [T1 T2].
pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (a + len - 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr (a + len - 1)) 8 ltac:(lia)).
unfold kLowMemEnd, kHighShadowEnd in *. lia. }
rewrite Hms1.
eapply SRr_mono.
{ eapply (fwrite_core B LAWS TB ly S W regs0 regs1 (ms_mem ms1) md1 f fd wpos n src cval P bs Wb);
[ exact HAR1 | exact Hra0 | exact Hal16 | exact Hslo | exact Hshi
| intros a Ha; apply PM1; apply HpresE; exact Ha
| exact Hgp | exact Htp | exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q10 | exact Q11 | exact QK
| exact HF0' | exact HF1' | exact HHDR1 | reflexivity | exact HP1 | clear - HP0; lia
| exact Hf0 | exact Hfhi | exact Hfal | exact Hfd
| intros a Ha; split; [apply PM1; apply (proj1 (HBLK a Ha)) | apply (proj2 (HBLK a Ha))]
| exact HBstk | exact HBimg | exact HBam
| apply RAX; [clear - Hf0; lia | clear - HBam Hfhi; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HBra]
| apply HVX; [clear - Hf0; lia | clear; lia | clear - HBam Hfhi; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HBhull]
| exact HSRC1 | exact Hn | exact Hn1 | exact Hsrc0 | exact Hsrchi | exact HSf | exact HSstk | exact HSam
| apply RAX; [clear - Hsrc0; lia | clear - HSam Hsrchi Hn1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HSra]
| apply HVX; [clear - Hsrc0; lia | clear - Hn1; lia | clear - HSam Hsrchi Hn1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HShull]
| exact Hcan1' | exact Hcan2' | exact Hcv
| rewrite Ffds; exact HfdL | rewrite Ffs; exact HfsL | exact HSmax ]. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Wb' & P' & -> & HAR' & HPRES' & A10' & Evm & Elz & HOK & HCAT & HPL' & HHDR' & HP' & HFS' & HSO' & HFDS' & HFSo & HFR' & HPM').
split; [reflexivity|]. exists regs', mem', md', Wb', P'.
split; [reflexivity|]. split; [exact HAR'|]. split; [exact HPRES'|]. split; [exact A10'|].
split; [rewrite Evm; exact Fmaps|]. split; [rewrite Elz; exact Flazy|]. split; [exact (os_kept_trans _ _ _ (os_kept_sbm _ _ MF1) HOK)|].
split; [exact HCAT|]. split; [exact HPL'|]. split; [exact HHDR'|]. split; [exact HP'|]. split; [exact HFS'|].
split; [intros Hso; apply HSO'; rewrite Ffs; exact Hso|].
split; [rewrite HFDS', Ffds; reflexivity|]. split; [intros q Hq; rewrite (HFSo q Hq), Ffs; reflexivity|].
split.
- intros a Ha Hb Hs. fold H in HFR'. rewrite (HFR' a Ha Hb ltac:(rewrite FS; exact Hs)). apply AV1; [exact Ha | rewrite FS in Hs; exact Hs | clear - Hb FB; lia].
- intros a Hp. fold H in HPM'. apply HPM'. apply PM1. exact Hp.
Qed.
Lemma mode_cell_m1 : forall m b, YP09.chunk_ok tfibsegs E0 m b (YP09.mkChunk 136 (CVal 4 (SLit 18446744073709551615))) -> val_mem tfibsegs m (b + 136) 4 4294967295.
Proof.
intros m b Hc. apply (val_of_chunk_ok tfibsegs E0 m b 136 4 (SLit 4294967295) 4294967295); [ | reflexivity | cbn; lia | cbn; lia].
intros i Hi. destruct (Hc i Hi) as (bt & Hb1 & Hb2). exists bt. split; [|exact Hb2]. rewrite <- Hb1.
cbn [cbyte sv_denot YP09.c_off YP09.c_val YP09.c_len cv_len] in Hi |- *. f_equal. apply bv_eq.
unfold byte_of_word. rewrite !Z_to_bv_unsigned.
assert (Hk4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct Hk4 as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.
Lemma mode_cell_lit : forall m b, YP09.chunk_ok tfibsegs E0 m b (YP09.mkChunk 136 (CVal 4 (SLit 4294967295))) -> val_mem tfibsegs m (b + 136) 4 4294967295.
Proof. intros m b Hc. exact (val_of_chunk_ok tfibsegs E0 m b 136 4 (SLit 4294967295) 4294967295 Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). Qed.
Theorem fwrite_entry : SRr tfibsegs W (cfg_at tfibsegs FWR_ENTRY regs0 mem0 md0) EPOST.
Proof.
pose proof facts0E as (Hsp & FB & FS & HP0 & Lhi).
pose proof E0_facts as (EEreg & EEx & EE2 & EE13 & EE12 & EE10 & EE11 & EE32 & EE33 & EE41 & EE13u & EE41u & EE12u & EE10u).
assert (Hwr : f + 240 <= wpos <= f + 1264) by (subst wpos; rewrite ?FB in *; lia).
pose proof HFILE as [HST HWIN].
assert (HP : garr8 tfibsegs m0 (f + 240) P).
{ destruct HWIN as [(-> & _) | (_ & _ & _ & _ & HG & _)]; [intros i Hi; cbn in Hi; lia | unfold FILE_BUF_OFF in HG; exact HG]. }
assert (FRAME : forall fr ms1, YP09.r_base fr = Some 13%nat -> YP09.r_wlo fr = 0 -> YP09.r_whi fr = 232 ->
frame_of E0 (ss_mem (mkSS FWR_ENTRY regsE ([stkE; fr] ++ canR) None (mkFacts factsE [] []))) (ms_mem ms0) (ms_mem ms1) ->
forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms1 z = mem0 z).
{ intros fr ms1 Hb Hlo Hhi HF z Hz1 Hz2. apply (HF z). intros Hin.
destruct (in_wrange_two_b E0 (ss_mem (mkSS FWR_ENTRY regsE ([stkE; fr] ++ canR) None (mkFacts factsE [] []))) (bv_unsigned z) 2 (- FWR_STK) 0 sp0 13 0 232 f
ltac:(cbn [ss_mem windows map app stkE canR YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite Hb, Hlo, Hhi; vm_compute; reflexivity) EE2 EE13u Hin); rewrite ?FS in *; lia. }
change (cfg_at tfibsegs FWR_ENTRY regs0 mem0 md0) with (mkCfg ms0 md0).
destruct HWIN as [(HPnil & W32 & W40 & W56 & W136) | (W32 & W40 & W56 & W136 & HG & HL)].
-
unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1 in *.
assert (HS0 : st_ok tfibsegs E0 ssEF (restrict H ms0)).
{ apply (entry_st_ok fileEF). right. split; [reflexivity|]. split; [exact HPnil|]. repeat split; assumption. }
eapply SRr_bind; [exact (musl_phase W E0 _ _ _ ms0 md0 HS0 runF_eq)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
apply (core_tail eEF (SOff 13 240) (SLit 1024) (SLit 18446744073709551615) ms1 mat1 shapeF_ok HS1).
+ exact (FRAME fileEF ms1 eq_refl eq_refl eq_refl HF1).
+ rewrite (U_atom_off E0 13 f 240 EE13) by lia. subst wpos. rewrite HPnil. cbn. lia.
+ rewrite U_lit by lia. subst wpos. rewrite HPnil. cbn. lia.
+ exact mode_cell_m1.
+ exact HP.
-
unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1 in *.
assert (HS0 : st_ok tfibsegs E0 ssEB (restrict H ms0)).
{ apply (entry_st_ok fileEB). left. split; [reflexivity|]. split; [exact I|].
subst wpos. split; [replace (f + 1264) with (f + 240 + 1024) by lia; exact W32|]. split; [exact W40|]. split; [exact W56 | exact W136]. }
eapply SRr_bind; [exact (musl_phase W E0 _ _ _ ms0 md0 HS0 runB_eq)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
apply (core_tail eEB (SOff 41 0) (SAlu ALU_ADD (SOff 13 1264) (SMd M_MUL (SOff 41 0) (SLit (-1)))) (SLit 4294967295) ms1 mat1 shapeB_ok HS1).
+ exact (FRAME fileEB ms1 eq_refl eq_refl eq_refl HF1).
+ exact (U_atom E0 41 wpos EE41 ltac:(lia)).
+ rewrite U_SAlu, U_SMd, (U_atom_off E0 13 f 1264 EE13), (U_atom E0 41 wpos EE41), U_SLit by lia.
unfold zcanon, M64. cbn [zalu_raw zmd_raw].
replace (wpos * (-1 mod 2 ^ 64)) with ((- wpos) + wpos * 2 ^ 64) by (change (-1 mod 2 ^ 64) with (2 ^ 64 - 1); lia).
rewrite Z_mod_plus_full.
destruct (Z.eq_dec wpos 0) as [-> | Hnz]; [rewrite Z.mod_small by lia; lia|].
replace (- wpos) with ((2 ^ 64 - wpos) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (2 ^ 64 - wpos)) by lia.
replace (f + 1264 + (2 ^ 64 - wpos)) with ((f + 1264 - wpos) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
+ exact mode_cell_lit.
+ exact HP.
Qed.
End g.
End d.
