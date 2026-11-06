(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the builder's end P 0x81ed4 / P1 0x81ed8 of
   LLVMFuzzerTestOneInput (0x7ff88), pod.h:440-444 with fuzz.h:39-42. Proves no function (kind: segment lemma).
   THE CODE
     0x81ed4 ld s4,0xb0(s1)                       the shadow address of &pp->len (P only; P1 enters with it)
     0x81ed8 .. 0x81f40                           the check of pp->len, a4 = pp, the checks of the 4-byte store at pp,
                                                  the four `sb` of the top size word len - 8, s9 = F, s10 = pp + 0x4d18
     0x81f44 beqz in.n -> 0x820ac                 no input left: no corruption
     0x81f48 .. 0x81f68 c = p[0]; bne c & 15, 15  -> 0x820ac: no corruption
     0x81f6c .. 0x81f7c s8 = len; bltu s8, 9      -> 0x820b8 -> C2 0x820c0: no corruption
     0x81f80 bltu in.n, 3                         -> RT 0x82094 (no byte written)
     0x81f8c .. 0x81fc4 p[1], p[2]; beq in.n, 3   -> RT
     0x81fc8 .. 0x81fec p[3]; beqz p[3] & 7       -> RT
     0x81ff0 .. 0x82014                           a3 = 0, a2 = p[3] & 7, a4 = (p[2] << 8 | p[1]) remu (len - 8) + 8,
                                                  a0 = the cursor + 4, a5 = in.n - 4: R 0x82018 with kk = 0
   The proof splits on |r| (0, 1 or 2, 3, >= 4) and on the input's branches before it builds an entry state, so each
   arm is one engine run whose branch outcomes are the conds of its state (closed numerals only). The shadow bytes
   of pp->len, of the store at pp and of the input bytes read are shadow entries of the engine, so no check reaches
   its error path. w10t_leaf turns any arm's last state into the post cuts' common part; RPgPostReq.w10_tail
   finishes the 0x820ac arms. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW7bBase RPgPostK RPgPostReq RPgW6cKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ---- the symbolic state at P1 (closed numerals only) ----
   atoms: 9 R, 21 pp + 0x4000, 23 K, 27 pp; extra 32 len, 33 F, 34 the cursor, 35 what is left (|r| >= 4),
   36 .. 39 the input bytes at the cursor *)
Definition w10t_sh21 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0).
Definition w10t_sr : list sv := sr_set sr_atoms (Z_to_bv 5 20) w10t_sh21.
Definition w10t_rtop : YP09.region := YP09.mkRegion (Some 27%nat) 0 4 0 4 [].
Definition w10t_rlen : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition w10t_rR (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 0x10 0x100 0 0
  ([YP09.mkChunk 0x10 (CVal 8 (SLit 0)); YP09.mkChunk 0x18 (CVal 8 (SOff 27 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x78 (CVal 8 (SOff 27 0x4d14)); YP09.mkChunk 0xb0 (CVal 8 w10t_sh21)] ++ cs).
Definition w10t_rin (k : nat) : YP09.region := YP09.mkRegion (Some 34%nat) 0 (Z.of_nat k) 0 0
  (map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (36 + i) 0))) (seq 0 k)).
Definition w10t_G0 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (27%nat, mkAF 4096 W10_HI 4); (32%nat, mkAF 8 5440 0)].
(* |r| = 0 *)
Definition w10t_ss0 : sstate := mkSS 0x81ed8 w10t_sr
  [w10t_rtop; w10t_rR [YP09.mkChunk 0xf8 (CVal 8 (SLit 0))]; w10t_rlen] None (mkFacts w10t_G0 [] []).
(* |r| >= 1: k input bytes known at the cursor (atom 34), what is left in [nlo, nhi] (atom 35), the cursor at most
   chi; conds carries the outcome of the input-dependent branches of the arm *)
Definition w10t_Gb (k : nat) : list (nat * afact) := map (fun i => ((36 + i)%nat, mkAF 0 255 0)) (seq 0 k).
Definition w10t_ssk (k : nat) (nlo nhi chi : Z) (conds : list acond) : sstate := mkSS 0x81ed8 w10t_sr
  [w10t_rtop; w10t_rR [YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 35 0))]; w10t_rlen;
   w10t_rin k] None
  (mkFacts (w10t_G0 ++ (34%nat, mkAF 1 chi 0) :: (35%nat, mkAF nlo nhi 0) :: w10t_Gb 4) conds []).
(* the branches on the input: 0x81f68 `bne` on c & 15 against 15, 0x81f7c `bltu` on len against 9, 0x81fc4 `beq`
   on what is left against 3, 0x81fec `beqz` on the count byte & 7 *)
Definition w10t_cNE15 : acond := mkAC BC_NE (SAlu ALU_AND (SOff 36 0) (SLit 15)) (SLit 15).
Definition w10t_cEQ15 : acond := mkAC BC_EQ (SAlu ALU_AND (SOff 36 0) (SLit 15)) (SLit 15).
Definition w10t_cLT9 : acond := mkAC BC_LTU (SOff 32 0) (SLit 9).
Definition w10t_cGE9 : acond := mkAC BC_GEU (SOff 32 0) (SLit 9).
Definition w10t_cEQ3 : acond := mkAC BC_EQ (SOff 35 0) (SLit 3).
Definition w10t_cEQ7 : acond := mkAC BC_EQ (SAlu ALU_AND (SOff 39 0) (SLit 7)) (SLit 0).
Definition w10t_cNE7 : acond := mkAC BC_NE (SAlu ALU_AND (SOff 39 0) (SLit 7)) (SLit 0).

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma w10t_in_byte : forall (H : word -> bool) mem src rest r i,
  garr8 rsegs (mrestrict H mem) src (rs_u8s rest) -> rs_suffix rest r -> (i < length r)%nat ->
  val_mem rsegs (mrestrict H mem) (src + Z.of_nat (length rest) - Z.of_nat (length r) + Z.of_nat i) 1
    (bv_unsigned (nth i r (Z_to_bv 8 0))).
Proof.
intros H mem src rest r i G (j & Hj & ->) Hi.
rewrite length_skipn in *.
assert (Hji : (j + i < length rest)%nat) by lia.
destruct (G (j + i)%nat) as [V _]; [unfold rs_u8s; rewrite length_map; exact Hji|].
unfold rs_u8s in V. rewrite rm_nth_map in V. rewrite nth_skipn.
replace (src + Z.of_nat (length rest) - Z.of_nat (length rest - j) + Z.of_nat i) with (src + Z.of_nat (j + i)) by lia.
replace (i + j)%nat with (j + i)%nat by lia. exact V.
Qed.

(* an 8-byte chunk from a cut's cell fact (RPgBase.rl_at: the value mod 2^64) *)
Lemma w10t_ch8 : forall E m R off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem rsegs m (R + off) 8 (v mod 2 ^ 64) -> YP09.chunk_ok rsegs E m R (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m R off e v He Hv V. rewrite Z.mod_small in V by lia.
apply (chunk_ok_val rsegs E m R off 8 e v He); [cbn; lia | cbn; lia | exact V].
Qed.

(* ---- the top size word read back out of the engine's region at atom 27 ---- *)
Lemma w10t_le_byte : forall v k, 0 <= v < 2 ^ 32 ->
  Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v 4 k).
Proof.
intros v k Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v) by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma w10t_chunk_byte : forall E m b o e w, YP09.chunk_ok rsegs E m b (YP09.mkChunk o (CVal 1 e)) ->
  bv_unsigned (sv_denot E e) = w -> mbyte rsegs m (b + o) = Some (Z_to_bv 8 w).
Proof.
intros E m b o e w Hc Hw. destruct (Hc 0) as (x & Hx & Hm); [cbn; lia|].
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hx, Hm. unfold byte_of_word in Hx.
rewrite Z.mul_0_r, Z.shiftr_0_r, Hw in Hx. injection Hx as <-. rewrite Z.add_0_r in Hm. exact Hm.
Qed.

Lemma w10t_top_val : forall E m cs L pp,
  region_ok rsegs E m (YP09.mkRegion (Some 27%nat) 0 4 0 4 cs) ->
  bv_unsigned (ew E 27) = pp -> ew E 32 = Z_to_bv 64 L -> 8 <= L <= 5440 ->
  In (YP09.mkChunk 0 (CVal 1 (SOff 32 (-8)))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 32 (-8)) (SLit 8)))) cs ->
  In (YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 32 (-8)) (SLit 16)))) cs ->
  In (YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 32 (-8)) (SLit 24)))) cs ->
  val_mem rsegs m pp 4 (L - 8).
Proof.
intros E m cs L pp HR H27 H32 HL I0 I1 I2 I3.
destruct HR as (_ & _ & _ & Hcs). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite H27 in Hcs.
assert (U0 : U E (SOff 32 (-8)) = L - 8) by (apply (U_atom_off E 32 L (-8) H32); lia).
assert (Us : forall s, 0 <= s < 64 -> U E (SAlu ALU_SRL (SOff 32 (-8)) (SLit s)) = Z.shiftr (L - 8) s).
{ intros s Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite U0, U_SLit. rewrite (zcanon_id s) by (unfold M64; lia).
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small s) by (change (2 ^ 6) with 64; lia).
  apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert ((L - 8) / 2 ^ s <= L - 8) by (apply Z.div_le_upper_bound; nia).
  assert (0 <= (L - 8) / 2 ^ s) by (apply Z.div_pos; lia). unfold M64. lia. }
pose proof (proj1 (Forall_forall _ _) Hcs) as Hc.
intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (pp + Z.of_nat 0) with (pp + 0).
  rewrite (w10t_chunk_byte E m pp 0 _ (L - 8) (Hc _ I0) U0).
  rewrite <- (w10t_le_byte (L - 8) 0) by lia. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- change (pp + Z.of_nat 1) with (pp + 1).
  rewrite (w10t_chunk_byte E m pp 1 _ _ (Hc _ I1) (Us 8 ltac:(lia))).
  rewrite <- (w10t_le_byte (L - 8) 1) by lia. reflexivity.
- change (pp + Z.of_nat 2) with (pp + 2).
  rewrite (w10t_chunk_byte E m pp 2 _ _ (Hc _ I2) (Us 16 ltac:(lia))).
  rewrite <- (w10t_le_byte (L - 8) 2) by lia. reflexivity.
- change (pp + Z.of_nat 3) with (pp + 3).
  rewrite (w10t_chunk_byte E m pp 3 _ _ (Hc _ I3) (Us 24 ltac:(lia))).
  rewrite <- (w10t_le_byte (L - 8) 3) by lia. reflexivity.
Qed.

(* a register at the end of a run, through the agreement of the run's environment with the entry one *)
Lemma w10t_reg : forall E0 E ss ms (H : word -> bool) (r : bv 5) k v w,
  st_ok rsegs E ss (restrict H ms) -> env_agree k E0 E -> sr_get (ss_regs ss) r = v -> sv_atoms_lt k v = true ->
  sv_denot E0 v = w -> getr (ms_regs ms) r = w.
Proof.
intros E0 E ss ms H r k v w HS HA Hv Hk Hw.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hv, (sv_denot_agree k E0 E v HA Hk). exact Hw.
Qed.

(* ---- the semantic end of every arm: what a run from P1 that wrote the top size word leaves ---- *)
Lemma w10t_leaf : forall cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  rs_pre rsegs B cx ->
  rs_Pbody rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_P rsegs cx rest r) ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall rr : Z, In rr [2; 3; 4; 8; 9; 19; 21; 23; 27] -> getr regs3 (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)) ->
  getr regs3 (Z_to_bv 5 20) = w64 (shadow_addr (e_pp (x_e cx) + 0x4000)) ->
  getr regs3 (Z_to_bv 5 25) = w64 (e_F (x_e cx)) ->
  getr regs3 (Z_to_bv 5 26) = w64 (e_pp (x_e cx) + 0x4d18) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx)) 4 (rs_plen sh ps - 8) ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 /\
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_post rsegs cx) /\
  rs_fsh_at rsegs cx W2 mem3 rs_P0 /\
  rs_pp_at rsegs cx W2 mem3 (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false).
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HP HB HL HJ3 Hio Hk R20 R25 R26 HK HV.
destruct HB as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & _).
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
unfold T_SEG_STK, ASTACK in HSTK.
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
assert (HL3 : rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_P rsegs cx rest r)).
{ apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HL).
  intros f Hf. unfold rs_L_P, rs_cur2 in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
    first [ solve [apply Hk; repeat first [left; reflexivity | right]]
          | solve [intros i Hi; apply HK; lia] ] |]).
  destruct Hf. }
unfold rs_at_cx, rs_at, rs_L_P, rs_cur2 in HL3. cbv zeta in HL3. cbn [app] in HL3.
rewrite !Forall_cons_iff in HL3.
destruct HL3 as (P8 & P9 & P19 & P23 & P21 & P27 & Q08 & Q10 & Q18 & Q28 & Q30 & Q68 & Q78 & Q80 & Qb0 & Qc8 & Qf8 & _).
split; [|split; [|split]].
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (fun a => e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) HC HJ3).
  + intros rr Hr. apply Hk. destruct Hr as [->|[->| ->]]; repeat first [left; reflexivity | right].
  + exact Hio.
  + exact HK.
  + intros a Ha. right. unfold PP_SIZE. lia.
- unfold rs_at_cx, rs_at, rs_L_post. cbv zeta.
  repeat apply Forall_cons;
  [exact P8 | exact P9 | exact P19 | exact P23 | exact P21 | exact P27 | exact R25 | exact R20 | exact R26
  | exact Q08 | exact Q28 | exact Q30 | exact Q68 | exact Q78 | exact Q80 | apply Forall_nil].
- apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. change (length rs_P0) with 52%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)).
  assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia|].
  pose proof (w10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs. unfold PP_SIZE in Hs. lia.
- rewrite <- (w10_img_top sh ps Hwf). unfold le32.
  assert (HLI : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
  { unfold pc_image. apply length_pp_image; [unfold POD_BUF_MAX in *; lia | |].
    - rewrite (pc_ents_final sh ps None). exact HW3.
    - rewrite (pc_ents_final sh ps None). exact HW4. }
  apply (rm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp (x_e cx)) _ 0 4 _ Hpp).
  + replace (e_pp (x_e cx) + Z.of_nat 0) with (e_pp (x_e cx)) by lia. exact HV.
  + unfold PP_SIZE in HLI. lia.
  + intros y Hy Hn. rewrite HLI in Hy. unfold PP_SIZE in Hy. apply HK; [lia|]. cbn in Hn. lia.
Qed.

(* ---- the common start of every arm: the cut's facts, by name ---- *)
Ltac w10t_pre HP HB HL :=
  pose proof HB as HB0;
  destruct HB as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hnps & Hps);
  pose proof RPgCfgChanges.cfg_wx as Hwx; pose proof RPgCfgChanges.cfg_segs_low as Hsegs;
  pose proof (AR_laws_ok rsegs B) as LAWS;
  destruct (w10_ctx B MT _ _ _ _ _ _ _ HP HC)
    as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR);
  unfold T_SEG_STK, ASTACK in HSTK;
  destruct (w10_F_ctx B _ HP) as (HF1 & HF2 & HF3);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  destruct (w10_wf_facts _ _ Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5);
  pose proof HL as HL0;
  unfold rs_at_cx, rs_at, rs_L_P, rs_cur2 in HL; cbv zeta in HL; cbn [app] in HL;
  rewrite !Forall_cons_iff in HL;
  destruct HL as (P8 & P9 & P19 & P23 & P21 & P27 & Q08 & Q10 & Q18 & Q28 & Q30 & Q68 & Q78 & Q80 & Qb0 & Qc8 & Qf8 & P20 & _);
  cbn [fst snd rl_at rl_xv] in P8, P9, P19, P23, P21, P27, Q08, Q10, Q18, Q28, Q30, Q68, Q78, Q80, Qb0, Qc8, Qf8, P20;
  pose proof HC as (HJ & _).

(* the len cell of the first block *)
Lemma w10t_len_cell : forall cx sh ps W2 mem2, rs_wf sh ps ->
  rs_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps None)) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (rs_plen sh ps).
Proof.
intros cx sh ps W2 mem2 Hwf Hpp. destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
unfold rs_pp_at, pc_image in Hpp. rewrite (pc_ents_final sh ps None) in Hpp.
exact (rm_pp_len rsegs (pc_buf (PbCut sh ps None)) _ _ _ _ _ ltac:(unfold POD_BUF_MAX; lia) HW3 HW4
  (w_H W2) mem2 (e_pp (x_e cx)) Hpp).
Qed.

Definition w10t_clob : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 24; 25; 26; 28; 29; 30; 31]%bv.

(* the shadow entry of k input bytes at an atom: their shadow bytes say they are addressable, and they lie in the
   application's memory, apart from the shadow span *)
Lemma w10t_shent_in : forall E m n src left c k, amem_range src left -> U E W10Bx = SHADOW_OFF ->
  U E (SOff n 0) = c -> src <= c -> c + k <= src + left -> 0 < k ->
  range_addressable (rd_of rsegs m) SHADOW_OFF src left ->
  shent_ok rsegs W10Bx E m (mkSHE n 0 k).
Proof.
intros E m n src left c k Ham HB Hc H1 H2 Hk Hra. split; cbn [she_m she_lo she_hi].
- rewrite HB, Hc. eapply range_addressable_sub; [exact Hra | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. rewrite Hc in Ha.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* ---- the input bytes at the cursor, at the cut's memory ---- *)
Lemma w10t_in_at : forall cx rest r (W2 : world rsegs) mem2 i,
  rs_in rsegs cx rest ->
  garr8 rsegs (mrestrict (w_H W2) mem2) (e_src (x_e cx)) (rs_u8s rest) ->
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)) ->
  rs_suffix rest r -> (i < length r)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (rs_cur rsegs cx rest r + Z.of_nat i) 1
    (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (rs_cur rsegs cx rest r + Z.of_nat i) 1 /\
  ~ (e_R (x_e cx) <= rs_cur rsegs cx rest r + Z.of_nat i < e_R (x_e cx) + 0x138) /\
  ~ (e_pp (x_e cx) <= rs_cur rsegs cx rest r + Z.of_nat i < e_pp (x_e cx) + PP_SIZE) /\
  e_src (x_e cx) <= rs_cur rsegs cx rest r + Z.of_nat i < e_src (x_e cx) + e_left (x_e cx).
Proof.
intros cx rest r W2 mem2 i HI G Hra Hsuf Hi.
pose proof Hsuf as (j & Hj & Hr).
assert (Hlr : length r = (length rest - j)%nat) by (rewrite Hr, length_skipn; reflexivity).
pose proof HI as (Hleft & _ & _ & _ & _ & _ & _ & Hdisj).
unfold rs_cur.
assert (Hx : e_src (x_e cx) <= e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r) + Z.of_nat i
  < e_src (x_e cx) + e_left (x_e cx)) by lia.
destruct (Hdisj _ Hx) as (D1 & D2 & D3).
split; [exact (w10t_in_byte _ _ _ _ _ _ G Hsuf Hi)|].
split.
{ replace (e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r) + Z.of_nat i)
    with (e_src (x_e cx) + (Z.of_nat (length rest) - Z.of_nat (length r) + Z.of_nat i)) by lia.
  apply (rm_in_ra _ _ _ _ _ Hra). lia. }
split; [|split; [exact D3 | exact Hx]].
intros X. apply D2. unfold rl_inw. cbn [hi_w1 role_himg_A].
apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.

(* ---- the region of R's cells and the facts every entry state shares ---- *)
Lemma w10t_rR_ok : forall E (H : word -> bool) mem R pp F cs,
  bv_unsigned (ew E 9) = R -> ew E 21 = Z_to_bv 64 (pp + 0x4000) -> ew E 23 = Z_to_bv 64 SHADOW_OFF ->
  ew E 27 = Z_to_bv 64 pp -> ew E 33 = Z_to_bv 64 F ->
  0 <= R -> R + 0x100 <= 2 ^ 64 -> 0 <= pp -> pp + 0x4d20 <= 2 ^ 47 -> 0 <= F < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) (R + 0x10) 8 (0 mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x18) 8 (pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x28) 8 (F mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x78) 8 ((pp + 0x4d14) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0xb0) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
  Forall (YP09.chunk_ok rsegs E (mrestrict H mem) R) cs ->
  region_ok rsegs E (mrestrict H mem) (w10t_rR cs).
Proof.
intros E H mem R pp F cs E9 E21 E23 E27 E33 HR0 HR1 Hp0 Hp1 HF Q10 Q18 Q28 Q78 Qb0 Hcs.
apply (rm_ro_region rsegs E H mem 9 R); [exact E9 | lia | lia |].
unfold w10t_rR. apply Forall_app. split; [|exact Hcs].
repeat apply Forall_cons; [..|apply Forall_nil].
- apply (w10t_ch8 _ _ _ _ _ 0); [reflexivity | lia | exact Q10].
- apply (w10t_ch8 _ _ _ _ _ pp); [exact (w10_den_atom _ 27 _ E27) | lia | exact Q18].
- apply (w10t_ch8 _ _ _ _ _ F); [exact (w10_den_atom _ 33 _ E33) | lia | exact Q28].
- apply (w10t_ch8 _ _ _ _ _ (pp + 0x4d14)); [exact (w10_den_off _ 27 _ _ E27) | lia | exact Q78].
- apply (w10t_ch8 _ _ _ _ _ (shadow_addr (pp + 0x4000)));
  [exact (w10_den_sh _ 21 23 _ E21 ltac:(lia) E23) | | exact Qb0].
  unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)).
  assert ((pp + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma w10t_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2. induction l1 as [|[n f] l IH]; cbn; [auto | intros [H1 H2] H; split; auto]. Qed.

Lemma w10t_G0_ok : forall E R pp L,
  bv_unsigned (ew E 9) = R -> ew E 21 = Z_to_bv 64 (pp + 0x4000) -> ew E 23 = Z_to_bv 64 SHADOW_OFF ->
  ew E 27 = Z_to_bv 64 pp -> ew E 32 = Z_to_bv 64 L ->
  2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> 4096 <= pp -> pp + 0x4000 <= W10_HI -> pp mod 16 = 0 -> 8 <= L <= 5440 ->
  atoms_ok E w10t_G0.
Proof.
intros E R pp L E9 E21 E23 E27 E32 HR HR16 Hp0 Hp1 Hal HL.
unfold w10t_G0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E21, E23, E27, E32, !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI in *; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (Hm : (pp + 0x4000) mod 16 = 0) by (rewrite Z.add_mod by lia; rewrite Hal; reflexivity).
unfold SHADOW_OFF, W10_HI in *. repeat split; try assumption; try lia.
Qed.

(* ---- |r| = 0: no corruption; 0x81f44 beqz -> 0x820ac, then RPgPostReq.w10_tail ---- *)
Lemma w10t_P1_0 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps,
  rs_pre rsegs B cx -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_cut_P1 rsegs B MT cx sh np ps rest [] ly2 S2 W2 regs2 mem2 md2 ->
  SRr rsegs W2 (cfg_at rsegs RS_P1 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps HP HC2 (HB & HL).
w10t_pre HP HB HL.
pose proof (w10t_len_cell cx sh ps W2 mem2 Hwf Hpp) as HLv. unfold rs_plen in HLv.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
remember (Ereg regs2 [Z_to_bv 64 L; Z_to_bv 64 (e_F (x_e cx))]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E21 : ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E27 : ew E 27 = Z_to_bv 64 (e_pp (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (e_F (x_e cx))) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (HS : st_ok rsegs E w10t_ss0 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    unfold w10t_sh21. rewrite (w10_den_sh _ 21 23 (e_pp (x_e cx) + 0x4000) E21 ltac:(lia) E23). exact P20.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (rm_rw_region rsegs _ (w_H W2) mem2 27 (e_pp (x_e cx)));
      [rewrite E27; apply unsigned_lit_small; lia | lia | lia | intros o Ho; apply Hpres; lia | constructor].
    + apply (rm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      unfold w10t_rR. cbn [app].
      change (Z.of_nat (length (@nil byte))) with 0 in Qf8.
      repeat apply Forall_cons; [..|apply Forall_nil].
      * apply (w10t_ch8 _ _ _ _ _ 0); [reflexivity | lia | exact Q10].
      * apply (w10t_ch8 _ _ _ _ _ (e_pp (x_e cx))); [exact (w10_den_atom _ 27 _ E27) | lia | exact Q18].
      * apply (w10t_ch8 _ _ _ _ _ (e_F (x_e cx))); [exact (w10_den_atom _ 33 _ E33) | lia | exact Q28].
      * apply (w10t_ch8 _ _ _ _ _ (e_pp (x_e cx) + 0x4d14)); [exact (w10_den_off _ 27 _ _ E27) | lia | exact Q78].
      * apply (w10t_ch8 _ _ _ _ _ (shadow_addr (e_pp (x_e cx) + 0x4000)));
        [exact (w10_den_sh _ 21 23 _ E21 ltac:(lia) E23) | unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (e_pp (x_e cx) + 0x4000) 8); assert ((e_pp (x_e cx) + 0x4000) / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia); lia | exact Qb0].
      * apply (w10t_ch8 _ _ _ _ _ 0); [reflexivity | lia | exact Qf8].
    + apply (rm_ro_region rsegs _ (w_H W2) mem2 21 (e_pp (x_e cx) + 0x4000)); [rewrite E21; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (e_pp (x_e cx) + 0x4000) 0 8 (SOff 32 0) L).
      * exact (w10_den_atom _ 32 L E32). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact HLv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w10t_rtop w10t_rR w10t_rlen].
    rewrite E27, E9, E21, !unsigned_lit_small by lia. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok]. unfold w10t_G0. cbn [atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite E9, E21, E23, E27, E32, !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    assert (Hm : (e_pp (x_e cx) + 0x4000) mod 16 = 0) by (rewrite Z.add_mod by lia; rewrite Hal; reflexivity).
    unfold SHADOW_OFF, W10_HI in *. repeat split; try lia. }
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 27 0 4] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 27 0 4 HAR Hinp);
  change (req_size PP_SIZE) with 19744;
  [exact Happ | exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)) | | | lia];
  rewrite (w10_U_atom E 27 _ E27 ltac:(lia)); lia. }
assert (HAE0 : env_agree 34 E E) by apply env_agree_refl.
unfold cfg_at. change (w64 RS_P1) with (Z_to_bv 64 0x81ed8).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820ac.
{ apply (w10_ob_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE (e_pp (x_e cx) + 0x4000) 8 (SOff 21 0) HAR Hinp);
  [lia | change (req_size PP_SIZE) with 19744; lia
  | exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia))
  | exact (w10_U_atom E 21 _ E21 ltac:(lia))]. }
{ unfold w10t_ss0. cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 27%nat (e_pp (x_e cx)) (e_pp (x_e cx)));
  [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | awr_ok_tac].
  rewrite E27. apply unsigned_lit_small. lia. }
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ =>
  assert (HAE : env_agree 34 E E') by env_agree_chain HAE0;
  assert (HAE32 : env_agree 32 (Ereg regs2 [Z_to_bv 64 L; Z_to_bv 64 (e_F (x_e cx))]) E')
    by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia) end.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb).
  unfold w10t_ss0 in Hr. cbn [ss_mem] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [w10t_rtop w10t_rR w10t_rlen YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
  [rewrite E27, unsigned_lit_small in Hrb by lia; lia | lia | lia]. }
pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2) w10t_clob HS HAE32 ltac:(vm_compute; reflexivity)) as RK.
assert (Hk : forall rr : Z, In rr [2; 3; 4; 8; 9; 19; 21; 23; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)).
{ intros rr Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity] |]).
  destruct Hr. }
assert (R20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (shadow_addr (e_pp (x_e cx) + 0x4000))).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 20) 34 w10t_sh21 _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  exact (w10_den_sh _ 21 23 _ E21 ltac:(lia) E23). }
assert (R25 : getr (ms_regs ms) (Z_to_bv 5 25) = w64 (e_F (x_e cx))).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 25) 34 (SOff 33 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  exact (w10_den_atom _ 33 _ E33). }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (e_pp (x_e cx) + 0x4d18)).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 26) 34 (SOff 27 0x4d18) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  exact (w10_den_off _ 27 _ _ E27). }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (e_pp (x_e cx)) 4 (rs_plen sh ps - 8)).
{ pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
  apply (w10t_top_val _ _ _ L (e_pp (x_e cx)) HR0).
  - rewrite (proj1 HAE 27%nat ltac:(lia)), E27. apply unsigned_lit_small. lia.
  - rewrite (proj1 HAE 32%nat ltac:(lia)). exact E32.
  - lia.
  - repeat first [left; reflexivity | right].
  - repeat first [left; reflexivity | right].
  - repeat first [left; reflexivity | right].
  - repeat first [left; reflexivity | right]. }
destruct (w10t_leaf cx sh np ps rest [] ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ HP HB0
  (proj1 (proj1 (Forall_app _ _ _) HL0))
  HJ (RPgCfgChanges.same_io_wvb _ _ _) Hk R20 R25 R26 HK HV) as (L1 & L2 & L3 & L4).
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (w10_tail B MT cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2 L1 L2 L3); [| exact Hlen].
rewrite (w10_build_tie rest sh np ps [] Hsh Hnp Hnps Hps), w10_corr_none_nil. exact L4.
Qed.

(* ======================================== |r| >= 1 ======================================== *)
Lemma w10t_rin_ok : forall E (H : word -> bool) mem cur (r : list byte) k,
  bv_unsigned (ew E 34) = cur -> 0 <= cur -> cur + Z.of_nat k <= 2 ^ 64 ->
  (forall i, (i < k)%nat -> ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  (forall i, (i < k)%nat ->
     val_mem rsegs (mrestrict H mem) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  region_ok rsegs E (mrestrict H mem) (w10t_rin k).
Proof.
intros E H mem cur r k H34 H0 H1 HE HV.
apply (rm_ro_region rsegs E H mem 34 cur); [exact H34 | lia | exact H1 |].
apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (i & <- & Hi). apply in_seq in Hi.
pose proof (rm_byte_range (nth i r (Z_to_bv 8 0))) as Hb.
apply (chunk_ok_val rsegs E _ cur (Z.of_nat i) 1 (SOff (36 + i) 0) (bv_unsigned (nth i r (Z_to_bv 8 0)))).
- apply w10_den_atom. apply HE. lia.
- cbn. lia.
- cbn. lia.
- apply HV. lia.
Qed.

Lemma w10t_Gb_ok : forall E (r : list byte) k,
  (forall i, (i < k)%nat -> ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  atoms_ok E (w10t_Gb k).
Proof.
intros E r k H. unfold w10t_Gb.
assert (G : forall s, (forall i, (s <= i < s + k)%nat ->
    ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  atoms_ok E (map (fun i => ((36 + i)%nat, mkAF 0 255 0)) (seq s k))).
{ clear H. induction k as [|k IH]; intros s Hs; cbn [seq map atoms_ok]; [exact I|]. split.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (Hs s ltac:(lia)).
    pose proof (rm_byte_range (nth s r (Z_to_bv 8 0))) as Hb. rewrite unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - apply IH. intros i Hi. apply Hs. lia. }
apply G. intros i Hi. apply H. lia.
Qed.

Lemma w10t_U_and15 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 15)) = v mod 16.
Proof.
intros E n v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia.
change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma w10t_U_and7 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 7)) = v mod 8.
Proof.
intros E n v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* a4 at R: (p[2] << 8 | p[1]) remu (len - 8) + 8 (0x81ff4 .. 0x8200c) *)
Lemma w10t_U_off : forall E xa xb L, ew E 37 = Z_to_bv 64 xa -> ew E 38 = Z_to_bv 64 xb ->
  ew E 32 = Z_to_bv 64 L -> 0 <= xa < 256 -> 0 <= xb < 256 -> 9 <= L <= 5440 ->
  U E (SAlu ALU_ADD (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 38 0) (SLit 8)) (SOff 37 0)) (SOff 32 (-8)))
    (SLit 8)) = 8 + (xa + 256 * xb) mod (L - 8).
Proof.
intros E xa xb L H37 H38 H32 Ba Bb HL.
assert (U37 : U E (SOff 37 0) = xa) by (apply U_atom; [exact H37 | lia]).
assert (U38 : U E (SOff 38 0) = xb) by (apply U_atom; [exact H38 | lia]).
assert (U32 : U E (SOff 32 (-8)) = L - 8) by (apply (U_atom_off E 32 L (-8) H32); lia).
assert (USL : U E (SAlu ALU_SLL (SOff 38 0) (SLit 8)) = Z.shiftl xb 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U38, U_SLit. change (Z.land (zcanon 8) 63) with 8.
  apply zcanon_id. rewrite Z.shiftl_mul_pow2 by lia. unfold M64. lia. }
assert (UOR : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 38 0) (SLit 8)) (SOff 37 0)) = xa + 256 * xb).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite USL, U37. rewrite Z.lor_comm, rm_lor_shift8 by lia.
  apply zcanon_id. unfold M64. lia. }
assert (UR : U E (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 38 0) (SLit 8)) (SOff 37 0)) (SOff 32 (-8)))
  = (xa + 256 * xb) mod (L - 8)).
{ rewrite U_SMd, UOR, U32. cbn [zmd_raw]. rewrite (proj2 (Z.eqb_neq (L - 8) 0)) by lia.
  pose proof (Z.mod_pos_bound (xa + 256 * xb) (L - 8) ltac:(lia)). apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite UR, U_SLit. change (zcanon 8) with 8.
pose proof (Z.mod_pos_bound (xa + 256 * xb) (L - 8) ltac:(lia)). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the model at the arms' ends ---- *)
Lemma w10t_model_RT : forall L (c0 : byte) r1, bv_unsigned c0 mod 16 = 15 -> 9 <= L ->
  fst (fuzz_u8 (skipn 2 r1)) mod 8 = 0 ->
  fst (corr_step L (c0 :: r1)) = Some (8 + fst (fuzz_u16 r1) mod (L - 8), []) /\
  8 <= 8 + fst (fuzz_u16 r1) mod (L - 8) < L.
Proof.
intros L c0 r1 Hc HL H0. pose proof (fuzz_u16_range r1) as Hu.
pose proof (Z.mod_pos_bound (fst (fuzz_u16 r1)) (L - 8) ltac:(lia)) as Hm.
split; [|lia]. rewrite (w10_corr_some L c0 r1 Hc ltac:(lia)). rewrite H0.
rewrite Z.min_l by lia. reflexivity.
Qed.

Lemma w10t_model_R : forall L (c0 xa xb xc : byte) r4 off cnt bs,
  bv_unsigned c0 mod 16 = 15 -> 9 <= L -> bv_unsigned xc mod 8 <> 0 ->
  off = 8 + (bv_unsigned xa + 256 * bv_unsigned xb) mod (L - 8) -> cnt = bv_unsigned xc mod 8 ->
  bs = fst (fuzz_u8s (Z.to_nat (Z.min cnt (L - off))) r4) ->
  fst (corr_step L (c0 :: xa :: xb :: xc :: r4)) = Some (off, bs) /\ 8 <= off < L /\ 0 < cnt <= 7 /\
  Z.of_nat (length bs) = Z.min cnt (L - off) /\ bs = fst (fuzz_u8s (length bs) r4).
Proof.
intros L c0 xa xb xc r4 off cnt bs Hc HL Hx Ho Hn Hb.
pose proof (rm_byte_range xa). pose proof (rm_byte_range xb). pose proof (rm_byte_range xc).
pose proof (Z.mod_pos_bound (bv_unsigned xa + 256 * bv_unsigned xb) (L - 8) ltac:(lia)) as Hm.
pose proof (Z.mod_pos_bound (bv_unsigned xc) 8 ltac:(lia)) as Hm8.
split; [|split; [lia|split; [lia|split]]].
- rewrite (w10_corr_some L c0 (xa :: xb :: xc :: r4) Hc ltac:(lia)). subst off cnt bs. reflexivity.
- rewrite Hb, w10_length_fuzz_u8s. rewrite Z2Nat.id; [reflexivity | lia].
- rewrite Hb at 1. rewrite Hb, w10_length_fuzz_u8s. reflexivity.
Qed.

(* ---- the targets' cuts from the leaf's four facts ---- *)
Lemma w10t_mkC2 : forall cx rest ly2 S2 W2 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ->
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_post rsegs cx) -> rs_fsh_at rsegs cx W2 mem3 rs_P0 ->
  rs_pp_at rsegs cx W2 mem3 (pp_bytes (fst (pod_build rest))) -> e_len (x_e cx) = rl_len rest ->
  getr regs3 (Z_to_bv 5 10) = w64 (e_len (x_e cx)) -> getr regs3 (Z_to_bv 5 24) = w64 (e_len (x_e cx)) ->
  rs_cut_C2 rsegs B MT cx rest ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest ly2 S2 W2 regs3 mem3 md3 L1 L2 L3 L4 Hlen R10 R24.
pose proof (rl_len_bounds rest) as Hb.
split; [exact L1|]. split; [apply (w10_L2_of_post cx (w_H W2) mem3 regs3 L2 R10 R24); lia|].
split; [exact L3|]. split; [exact L4 | exact Hlen].
Qed.

Lemma w10t_mkRT : forall cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off,
  rs_Pbody rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ->
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_post rsegs cx) -> rs_fsh_at rsegs cx W2 mem3 rs_P0 ->
  rs_pp_at rsegs cx W2 mem3 (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) ->
  fst (pod_build rest) = PodRec sh ps (Some (off, [])) -> 8 <= off -> off <= rs_plen sh ps ->
  rs_cut_RT rsegs B MT cx sh ps off [] rest r ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off HB L1 L2 L3 L4 Ht Ho1 Ho2.
destruct HB as (_ & _ & _ & Hin & Hsuf & Hwf & Hlen & _).
split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
split; [unfold rs_img_corr; cbn [length Z.of_nat Z.to_nat firstn]; rewrite w10_overwrite_nil; exact L4|].
split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Ht|].
split; [exact Ho1|]. cbn [length Z.of_nat]. split; lia.
Qed.

Lemma w10t_mkR : forall cx sh np ps rest r r' ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off bs cnt,
  rs_Pbody rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ->
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_post rsegs cx) -> rs_fsh_at rsegs cx W2 mem3 rs_P0 ->
  rs_pp_at rsegs cx W2 mem3 (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) ->
  getr regs3 (Z_to_bv 5 13) = w64 0 -> getr regs3 (Z_to_bv 5 12) = w64 cnt -> getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  rs_suffix rest r' -> fst (pod_build rest) = PodRec sh ps (Some (off, bs)) -> rs_corr_wf sh ps off bs cnt ->
  bs = fst (fuzz_u8s (length bs) r') ->
  rs_cut_R rsegs B MT cx sh ps rest r' off bs cnt 0 ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx sh np ps rest r r' ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off bs cnt HB L1 L2 L3 L4
  R13 R12 R14 R10 R15 Hsuf' Ht Hcw Hbs.
destruct HB as (_ & _ & _ & Hin & _ & Hwf & Hlen & _).
pose proof Hcw as (_ & _ & _ & Hcnt & _).
split; [exact L1|]. split.
{ unfold rs_at_cx, rs_at in *. apply Forall_app. split; [exact L2|].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd rl_at].
  - exact R13. - rewrite Z.sub_0_r. exact R12. - exact R14. - exact R10. - exact R15. }
split; [exact L3|].
split; [unfold rs_img_corr; cbn [Z.to_nat firstn]; rewrite w10_overwrite_nil; exact L4|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Ht|].
split; [exact Hcw|]. split; [lia|]. split; [lia|].
cbn [Z.to_nat skipn]. rewrite Nat.sub_0_r. exact Hbs.
Qed.

(* ---- one arm's entry state (|r| >= 1; the arm's branch outcomes are the conds of its state) ---- *)
Lemma w10t_HS_lem : forall (cx : rs_scx rsegs) (rest r : list byte) (W2 : world rsegs) regs2 mem2 E ex L cur F k
  nlo nhi chi conds,
  E = Ereg regs2 ex ->
  ew E 9 = Z_to_bv 64 (e_R (x_e cx)) -> ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000) ->
  ew E 23 = Z_to_bv 64 SHADOW_OFF -> ew E 27 = Z_to_bv 64 (e_pp (x_e cx)) -> ew E 32 = Z_to_bv 64 L ->
  ew E 33 = Z_to_bv 64 F -> ew E 34 = Z_to_bv 64 cur -> ew E 35 = Z_to_bv 64 (Z.of_nat (length r)) ->
  (forall i, (i < 4)%nat -> ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  getr regs2 (Z_to_bv 5 20) = w64 (shadow_addr (e_pp (x_e cx) + 0x4000)) ->
  2 ^ 46 <= e_R (x_e cx) -> e_R (x_e cx) + 0x1a0 <= 2 ^ 47 -> e_R (x_e cx) mod 16 = 0 ->
  4096 <= e_pp (x_e cx) -> e_pp (x_e cx) + 19744 <= e_R (x_e cx) -> e_pp (x_e cx) mod 16 = 0 ->
  0 <= F < 2 ^ 64 -> 8 <= L <= 5440 ->
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + 19744 -> apresent (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x10) 8 (0 mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x18) 8 (e_pp (x_e cx) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x28) 8 (F mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x78) 8 ((e_pp (x_e cx) + 0x4d14) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xb0) 8 (shadow_addr (e_pp (x_e cx) + 0x4000) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xc8) 8 (cur mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xf8) 8 (Z.of_nat (length r) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 L ->
  (forall i, (i < k)%nat ->
     val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
     ~ (e_R (x_e cx) <= cur + Z.of_nat i < e_R (x_e cx) + 0x138) /\
     ~ (e_pp (x_e cx) <= cur + Z.of_nat i < e_pp (x_e cx) + PP_SIZE)) ->
  (0 < k <= 4)%nat -> 1 <= cur <= chi -> chi + 4 <= 2 ^ 64 ->
  nlo <= Z.of_nat (length r) <= nhi -> Z.of_nat (length r) < 2 ^ 64 ->
  regions_wf [w10t_rtop; w10t_rR [YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 35 0))];
    w10t_rlen; w10t_rin k] = true ->
  conds_ok E conds ->
  st_ok rsegs E (w10t_ssk k nlo nhi chi conds) (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs))).
Proof.
intros cx rest r W2 regs2 mem2 E ex L cur F k nlo nhi chi conds HE E9 E21 E23 E27 E32 E33 E34 E35 EB P20
  HR0 HR1 HR16 Hp0 HpR Hal HF HL Hpres Q10 Q18 Q28 Q78 Qb0 Qc8 Qf8 HLv HIN Hk Hc Hchi Hnl Hnl64 Hwf Hco.
assert (U9 : bv_unsigned (ew E 9) = e_R (x_e cx)) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = e_pp (x_e cx)) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = cur) by (rewrite E34; apply unsigned_lit_small; lia).
destruct (HIN 0%nat ltac:(lia)) as (_ & NRa & NPa).
destruct (HIN (k - 1)%nat ltac:(lia)) as (_ & NRb & NPb).
rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
  unfold w10t_sh21. rewrite (w10_den_sh _ 21 23 (e_pp (x_e cx) + 0x4000) E21 ltac:(lia) E23). exact P20.
- exact Hwf.
- apply Forall_cons.
  { apply (rm_rw_region rsegs _ (w_H W2) mem2 27 (e_pp (x_e cx)));
    [exact U27 | lia | lia | intros o Ho; apply Hpres; lia | constructor]. }
  apply Forall_cons.
  { apply (w10t_rR_ok _ _ _ _ _ F _ U9 E21 E23 E27 E33); try lia; try assumption.
    apply Forall_cons; [apply (w10t_ch8 _ _ _ _ _ cur); [exact (w10_den_atom _ 34 _ E34) | lia | exact Qc8] |].
    apply Forall_cons; [apply (w10t_ch8 _ _ _ _ _ (Z.of_nat (length r))); [exact (w10_den_atom _ 35 _ E35) | lia | exact Qf8] |].
    apply Forall_nil. }
  apply Forall_cons.
  { apply (rm_ro_region rsegs _ (w_H W2) mem2 21 (e_pp (x_e cx) + 0x4000));
      [rewrite E21; apply unsigned_lit_small; lia | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (e_pp (x_e cx) + 0x4000) 0 8 (SOff 32 0) L);
      [exact (w10_den_atom _ 32 L E32) | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HLv]. }
  apply Forall_cons; [| apply Forall_nil].
  apply (w10t_rin_ok _ _ _ cur r); [exact U34 | lia | lia | intros i Hi; apply EB; lia | intros i Hi; exact (proj1 (HIN i Hi))].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w10t_rtop w10t_rR w10t_rlen w10t_rin].
  rewrite U9, U34, U27, E21, !unsigned_lit_small by lia.
  unfold PP_SIZE in *. repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split; [exact Hco | cbn; exact I]].
  apply w10t_atoms_app; [apply (w10t_G0_ok _ (e_R (x_e cx)) (e_pp (x_e cx)) L U9 E21 E23 E27 E32); unfold W10_HI; lia|].
  cbn [atoms_ok]. split.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U34. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
  split.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E35, unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
  exact (w10t_Gb_ok _ r 4 EB).
Qed.

(* ---- one arm's end: the leaf's four facts from the run's last state ---- *)
Lemma w10t_fin_lem : forall cx sh np ps rest r ly2 S2 (W2 : world rsegs) regs2 mem2 md2 E ex E' ss ms md3 rs0 cs,
  rs_pre rsegs B cx -> rs_Pbody rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_P rsegs cx rest r) ->
  E = Ereg regs2 ex ->
  ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000) -> ew E 23 = Z_to_bv 64 SHADOW_OFF ->
  ew E 27 = Z_to_bv 64 (e_pp (x_e cx)) -> ew E 32 = Z_to_bv 64 (rs_plen sh ps) ->
  ew E 33 = Z_to_bv 64 (e_F (x_e cx)) ->
  st_ok rsegs E' ss (restrict (w_H W2) ms) -> env_agree 40 E E' ->
  forallb (fun r0 : bv 5 => existsb (fun c => bv_eqb c r0) w10t_clob
    || sv_eqb (sr_get (ss_regs ss) r0) (SOff (Z.to_nat (bv_unsigned r0)) 0)) w7_nz_regs = true ->
  sr_get (ss_regs ss) (Z_to_bv 5 20) = w10t_sh21 -> sr_get (ss_regs ss) (Z_to_bv 5 25) = SOff 33 0 ->
  sr_get (ss_regs ss) (Z_to_bv 5 26) = SOff 27 0x4d18 ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 27%nat) 0 4 0 4 cs) ->
  In (YP09.mkChunk 0 (CVal 1 (SOff 32 (-8)))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 32 (-8)) (SLit 8)))) cs ->
  In (YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 32 (-8)) (SLit 16)))) cs ->
  In (YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 32 (-8)) (SLit 24)))) cs ->
  frame_of E rs0 (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)) ->
  (forall a, in_wrange E rs0 a -> e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 (ms_mem ms) md3 (x_k cx) ->
  same_io md2 md3 ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\
  rs_at_cx rsegs cx W2 (ms_mem ms) (ms_regs ms) (rs_L_post rsegs cx) /\
  rs_fsh_at rsegs cx W2 (ms_mem ms) rs_P0 /\
  rs_pp_at rsegs cx W2 (ms_mem ms) (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false).
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E ex E' ss ms md3 rs0 cs HP HB HL HE E21 E23 E27 E32 E33
  HS HAE Hck H20 H25 H26 Hnth I0 I1 I2 I3 HFr Hwr HJ Hio.
pose proof HB as (HC & _ & _ & _ & _ & Hwf & _).
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5). unfold rs_plen in *.
assert (HAE32 : env_agree 32 (Ereg regs2 ex) E') by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros X. exact (Hn (Hwr a X)). }
pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2) w10t_clob HS HAE32 Hck) as RK.
assert (Hk : forall rr : Z, In rr [2; 3; 4; 8; 9; 19; 21; 23; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)).
{ intros rr Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity] |]).
  destruct Hr. }
assert (R20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (shadow_addr (e_pp (x_e cx) + 0x4000))).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 20) 40 w10t_sh21 _ HS HAE H20); [reflexivity |].
  exact (w10_den_sh _ 21 23 _ E21 ltac:(lia) E23). }
assert (R25 : getr (ms_regs ms) (Z_to_bv 5 25) = w64 (e_F (x_e cx))).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 25) 40 (SOff 33 0) _ HS HAE H25); [reflexivity |].
  exact (w10_den_atom _ 33 _ E33). }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (e_pp (x_e cx) + 0x4d18)).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 26) 40 (SOff 27 0x4d18) _ HS HAE H26); [reflexivity |].
  exact (w10_den_off _ 27 _ _ E27). }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (e_pp (x_e cx)) 4
  (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8)).
{ apply (w10t_top_val _ _ _ _ (e_pp (x_e cx)) (w7_region_nth _ _ _ 0 _ HS Hnth)); [| | lia | exact I0 | exact I1 | exact I2 | exact I3].
  - rewrite (proj1 HAE 27%nat ltac:(lia)), E27. apply unsigned_lit_small. lia.
  - rewrite (proj1 HAE 32%nat ltac:(lia)). exact E32. }
exact (w10t_leaf cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) md3 HP HB HL HJ Hio
  Hk R20 R25 R26 HK HV).
Qed.

(* the conds of an arm, from its branch facts (EB, E32, E35: the entry environment's atoms) *)
Ltac w10t_cond1 EB E32 E35 :=
  unfold acond_ok, w10t_cNE15, w10t_cEQ15, w10t_cLT9, w10t_cGE9, w10t_cEQ3, w10t_cEQ7, w10t_cNE7;
  cbn [ac_c ac_a ac_b];
  first [ rewrite branch_ne_U | rewrite branch_eq_U | rewrite branch_ltu_U | rewrite branch_geu_U ];
  rewrite ?(w10t_U_and15 _ 36 _ (EB 0%nat ltac:(lia)) (rm_byte_range _)),
          ?(w10t_U_and7 _ 39 _ (EB 3%nat ltac:(lia)) (rm_byte_range _)),
          ?(w10_U_atom _ 32 _ E32 ltac:(lia)), ?(w10_U_atom _ 35 _ E35 ltac:(lia)), ?U_lit by lia;
  first [ apply negb_true_iff, Z.eqb_neq | apply Z.eqb_eq | apply Z.ltb_lt | apply negb_true_iff, Z.ltb_ge ];
  first [ assumption | lia ].
Ltac w10t_conds EB E32 E35 := cbn [conds_ok]; repeat first [ exact I | split; [w10t_cond1 EB E32 E35 |] ].

(* every write window of an entry state lies in [pp, pp + 4) *)
Ltac w10t_kwr :=
  intros ? (rg & Hr & Hrb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; lia |]);
  destruct Hr.

(* the In facts of the top word's chunks *)
Ltac w10t_in := repeat first [left; reflexivity | right].

(* the write windows of an entry state: the top size word at pp (atom 27), the rest read-only *)
Ltac w10t_awr E pp U27 Hinp Hfresh :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end;
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 27%nat pp pp);
  [reflexivity | exact U27 | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | awr_ok_tac].

Lemma w10t_split4 : forall (r : list byte), (4 <= length r)%nat ->
  exists c0 xa xb xc r4, r = c0 :: xa :: xb :: xc :: r4.
Proof. intros r H. destruct r as [|c0 [|xa [|xb [|xc r4]]]]; cbn [length] in H; try lia. eauto 6. Qed.

(* ---- |r| >= 4: c, the offset's two bytes and the count byte ---- *)
Lemma w10t_P1_4 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r,
  rs_pre rsegs B cx -> (forall kk, rs_from_R rsegs B MT cx POST rest kk) -> rs_from_RT rsegs B MT cx POST rest ->
  rs_from_C2 rsegs B MT cx POST rest ->
  rs_cut_P1 rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 -> (4 <= length r)%nat ->
  SRr rsegs W2 (cfg_at rsegs RS_P1 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HR HRT HC2 (HB & HL) Hr4.
w10t_pre HP HB HL.
pose proof (w10t_len_cell cx sh ps W2 mem2 Hwf Hpp) as HLv. unfold rs_plen in HLv.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
destruct (rs_in_now rsegs B MT cx rest rs_P0 ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl) as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof Hsuf as (jr & Hjr & Hrj).
assert (Hlr : (length r <= length rest)%nat) by (rewrite Hrj, length_skipn; lia).
set (cur := rs_cur rsegs cx rest r) in *.
assert (Hcd : cur = e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r)) by reflexivity.
assert (Hcur : 1 <= cur /\ cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (rewrite Hcd; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof (w10_build_tie rest sh np ps r Hsh Hnp Hnps Hps) as Htie.
assert (HLp : Z.of_nat (length (pod_encode (PodRec sh ps None))) = L) by (rewrite HW2; reflexivity).
rewrite HLp in Htie.
assert (HIN : forall i, (i < length r)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
  ~ (e_R (x_e cx) <= cur + Z.of_nat i < e_R (x_e cx) + 0x138) /\
  ~ (e_pp (x_e cx) <= cur + Z.of_nat i < e_pp (x_e cx) + PP_SIZE)).
{ intros i Hi. destruct (w10t_in_at cx rest r W2 mem2 i Hin Hbytes Hra Hsuf Hi) as (V & _ & N1 & N2 & _).
  split; [exact V|]. split; [exact N1 | exact N2]. }
remember (Ereg regs2 ([Z_to_bv 64 L; Z_to_bv 64 (e_F (x_e cx)); Z_to_bv 64 cur; Z_to_bv 64 (Z.of_nat (length r))]
  ++ map (fun i => Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) (seq 0 4))) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E21 : ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E27 : ew E 27 = Z_to_bv 64 (e_pp (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (e_F (x_e cx))) by (subst E; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 cur) by (subst E; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; reflexivity).
assert (EB : forall i, (i < 4)%nat -> ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))).
{ intros i Hi. subst E. destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
assert (U27 : bv_unsigned (ew E 27) = e_pp (x_e cx)) by (rewrite E27; apply unsigned_lit_small; lia).
assert (HB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)).
assert (HAE0 : env_agree 40 E E) by apply env_agree_refl.
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 27 0 4; mkSHE 21 0 8; mkSHE 34 0 4] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 27 0 4 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 27 _ E27 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia.
  - apply (w10t_shent_in E _ 34 (e_src (x_e cx)) (e_left (x_e cx)) cur 4 Hamr HB (w10_U_atom E 34 _ E34 ltac:(lia)));
    [lia | lia | lia | exact Hra]. }
destruct (w10t_split4 r Hr4) as (c0 & xa & xb & xc & r4 & Hr0).
pose proof (rm_byte_range c0) as Bc0. pose proof (rm_byte_range xa) as Bxa.
pose proof (rm_byte_range xb) as Bxb. pose proof (rm_byte_range xc) as Bxc.
unfold cfg_at. change (w64 RS_P1) with (Z_to_bv 64 0x81ed8).
destruct (Z.eq_dec (bv_unsigned (nth 0 r (Z_to_bv 8 0)) mod 16) 15) as [Hc15|Hc15].
2: { (* c & 15 <> 15: no corruption, 0x820ac *)
  assert (HS : st_ok rsegs E (w10t_ssk 4 4 (2 ^ 63) (2 ^ 47 - 5) [w10t_cNE15])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 4 4 (2 ^ 63) (2 ^ 47 - 5) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820ac; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (w10_tail B MT cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2 L1 L2 L3); [| exact Hlen].
  rewrite Hr0 in Hc15. cbn [nth] in Hc15.
  rewrite Htie, Hr0, (w10_corr_none L c0 _ (or_introl Hc15)). exact L4. }
destruct (Z_lt_le_dec L 9) as [HL9|HL9].
{ (* len < 9: no corruption, 0x820b8 -> C2 *)
  assert (HS : st_ok rsegs E (w10t_ssk 4 4 (2 ^ 63) (2 ^ 47 - 5) [w10t_cEQ15; w10t_cLT9])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 4 4 (2 ^ 63) (2 ^ 47 - 5) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820c0; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  assert (Hnone : fst (corr_step L r) = None) by (rewrite Hr0; apply w10_corr_none; right; lia).
  assert (HeL : e_len (x_e cx) = L).
  { rewrite Hlen. unfold rl_len. rewrite Htie, Hnone. cbn [buf p_corr]. rewrite HW2. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_len (x_e cx))).
  { apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 40 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (w10_den_atom _ 32 _ E32). }
  assert (R24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (e_len (x_e cx))).
  { apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 40 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (w10_den_atom _ 32 _ E32). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HC2 ly2 S2). apply (w10t_mkC2 cx rest ly2 S2 W2 _ _ _ L1 L2 L3); [| exact Hlen | exact R10 | exact R24].
  rewrite Htie, Hnone. exact L4. }
pose proof Hc15 as Hc15r. rewrite Hr0 in Hc15. cbn [nth] in Hc15.
destruct (Z.eq_dec (bv_unsigned (nth 3 r (Z_to_bv 8 0)) mod 8) 0) as [Hn0|Hn0].
{ (* the count byte & 7 = 0: no byte written, RT *)
  assert (HS : st_ok rsegs E (w10t_ssk 4 4 (2 ^ 63) (2 ^ 47 - 5) [w10t_cEQ15; w10t_cGE9; w10t_cEQ7])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 4 4 (2 ^ 63) (2 ^ 47 - 5) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  rewrite Hr0 in Hn0. cbn [nth] in Hn0.
  destruct (w10t_model_RT L c0 (xa :: xb :: xc :: r4) Hc15 HL9 ltac:(cbn; exact Hn0)) as (Hm & Hob).
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps (8 + fst (fuzz_u16 (xa :: xb :: xc :: r4)) mod (L - 8)) [] r).
  apply (w10t_mkRT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HB0 L1 L2 L3 L4);
  [rewrite Htie, Hr0, Hm; reflexivity | lia | unfold rs_plen; fold L; lia]. }
(* the count byte & 7 <> 0: the corruption loop, R with kk = 0 *)
assert (HS : st_ok rsegs E (w10t_ssk 4 4 (2 ^ 63) (2 ^ 47 - 5) [w10t_cEQ15; w10t_cGE9; w10t_cNE7])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
{ apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 4 4 (2 ^ 63) (2 ^ 47 - 5) _
    HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
  all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
             | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82018; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
  (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
  (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
pose proof Hn0 as Hn0r. rewrite Hr0 in Hn0. cbn [nth] in Hn0.
set (off := 8 + (bv_unsigned xa + 256 * bv_unsigned xb) mod (L - 8)).
set (cnt := bv_unsigned xc mod 8).
set (bs := fst (fuzz_u8s (Z.to_nat (Z.min cnt (L - off))) r4)).
destruct (w10t_model_R L c0 xa xb xc r4 off cnt bs Hc15 HL9 Hn0 eq_refl eq_refl eq_refl)
  as (Hm & Hoff & Hcnt & Hbl & Hbs).
assert (Hlr4 : length r = (4 + length r4)%nat) by (rewrite Hr0; reflexivity).
assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 0).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 13) 40 (SLit 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  reflexivity. }
assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 cnt).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 12) 40 (SAlu ALU_AND (SOff 39 0) (SLit 7)) _ HS HAE);
    [vm_compute; reflexivity | reflexivity |].
  rewrite denot_lit_U. rewrite (w10t_U_and7 E 39 _ (EB 3%nat ltac:(lia)) (rm_byte_range _)). rewrite Hr0. reflexivity. }
assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 14) 40
    (SAlu ALU_ADD (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 38 0) (SLit 8)) (SOff 37 0)) (SOff 32 (-8))) (SLit 8))
    _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite denot_lit_U.
  rewrite (w10t_U_off E (bv_unsigned xa) (bv_unsigned xb) L); [reflexivity | | | exact E32 | lia | lia | lia].
  - transitivity (Z_to_bv 64 (bv_unsigned (nth 1 r (Z_to_bv 8 0)))); [exact (EB 1%nat ltac:(lia)) | rewrite Hr0; reflexivity].
  - transitivity (Z_to_bv 64 (bv_unsigned (nth 2 r (Z_to_bv 8 0)))); [exact (EB 2%nat ltac:(lia)) | rewrite Hr0; reflexivity]. }
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest r4)).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 40 (SOff 34 4) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (w10_den_off _ 34 _ _ E34). unfold w64. f_equal. unfold rs_cur. rewrite Hcd, Hlr4. lia. }
assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r4))).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 15) 40 (SOff 35 (-4)) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (w10_den_off _ 35 _ _ E35). unfold w64. f_equal. rewrite Hlr4. lia. }
assert (Hsuf4 : rs_suffix rest r4).
{ exists (4 + jr)%nat. split; [rewrite Hrj, length_skipn in Hlr4; lia|].
  rewrite <- skipn_skipn, <- Hrj, Hr0. reflexivity. }
apply (HR 0%nat ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r4 off bs cnt).
apply (w10t_mkR cx sh np ps rest r r4 ly2 S2 W2 regs2 mem2 md2 _ _ _ off bs cnt HB0 L1 L2 L3 L4
  R13 R12 R14 R10 R15 Hsuf4); [rewrite Htie, Hr0, Hm; reflexivity | | exact Hbs].
unfold rs_corr_wf, rs_plen. fold L. lia.
Qed.

(* the input's first bytes, for the cases |r| = 3 and |r| >= 1 *)
Lemma w10t_split3 : forall (r : list byte), length r = 3%nat -> exists c0 xa xb, r = [c0; xa; xb].
Proof. intros r H. destruct r as [|c0 [|xa [|xb [|xc r4]]]]; cbn [length] in H; try lia. eauto. Qed.
Lemma w10t_split1 : forall (r : list byte), (1 <= length r)%nat -> exists c0 r1, r = c0 :: r1.
Proof. intros r H. destruct r as [|c0 r1]; cbn [length] in H; [lia | eauto]. Qed.

(* ---- |r| = 3: c and the offset's two bytes; the count byte reads 0 ---- *)
Lemma w10t_P1_3 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r,
  rs_pre rsegs B cx -> rs_from_RT rsegs B MT cx POST rest -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_cut_P1 rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 -> length r = 3%nat ->
  SRr rsegs W2 (cfg_at rsegs RS_P1 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HRT HC2 (HB & HL) Hr3.
w10t_pre HP HB HL.
pose proof (w10t_len_cell cx sh ps W2 mem2 Hwf Hpp) as HLv. unfold rs_plen in HLv.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
destruct (rs_in_now rsegs B MT cx rest rs_P0 ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl) as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof Hsuf as (jr & Hjr & Hrj).
assert (Hlr : (length r <= length rest)%nat) by (rewrite Hrj, length_skipn; lia).
set (cur := rs_cur rsegs cx rest r) in *.
assert (Hcd : cur = e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r)) by reflexivity.
assert (Hcur : 1 <= cur /\ cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (rewrite Hcd; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof (w10_build_tie rest sh np ps r Hsh Hnp Hnps Hps) as Htie.
assert (HLp : Z.of_nat (length (pod_encode (PodRec sh ps None))) = L) by (rewrite HW2; reflexivity).
rewrite HLp in Htie.
assert (HIN : forall i, (i < length r)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
  ~ (e_R (x_e cx) <= cur + Z.of_nat i < e_R (x_e cx) + 0x138) /\
  ~ (e_pp (x_e cx) <= cur + Z.of_nat i < e_pp (x_e cx) + PP_SIZE)).
{ intros i Hi. destruct (w10t_in_at cx rest r W2 mem2 i Hin Hbytes Hra Hsuf Hi) as (V & _ & N1 & N2 & _).
  split; [exact V|]. split; [exact N1 | exact N2]. }
remember (Ereg regs2 ([Z_to_bv 64 L; Z_to_bv 64 (e_F (x_e cx)); Z_to_bv 64 cur; Z_to_bv 64 (Z.of_nat (length r))]
  ++ map (fun i => Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) (seq 0 4))) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E21 : ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E27 : ew E 27 = Z_to_bv 64 (e_pp (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (e_F (x_e cx))) by (subst E; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 cur) by (subst E; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; reflexivity).
assert (EB : forall i, (i < 4)%nat -> ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))).
{ intros i Hi. subst E. destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
assert (U27 : bv_unsigned (ew E 27) = e_pp (x_e cx)) by (rewrite E27; apply unsigned_lit_small; lia).
assert (HB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)).
assert (HAE0 : env_agree 40 E E) by apply env_agree_refl.
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 27 0 4; mkSHE 21 0 8; mkSHE 34 0 3] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 27 0 4 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 27 _ E27 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia.
  - apply (w10t_shent_in E _ 34 (e_src (x_e cx)) (e_left (x_e cx)) cur 3 Hamr HB (w10_U_atom E 34 _ E34 ltac:(lia)));
    [lia | lia | lia | exact Hra]. }
destruct (w10t_split3 r Hr3) as (c0 & xa & xb & Hr0).
pose proof (rm_byte_range c0) as Bc0. pose proof (rm_byte_range xa) as Bxa. pose proof (rm_byte_range xb) as Bxb.
unfold cfg_at. change (w64 RS_P1) with (Z_to_bv 64 0x81ed8).
destruct (Z.eq_dec (bv_unsigned (nth 0 r (Z_to_bv 8 0)) mod 16) 15) as [Hc15|Hc15].
2: { (* c & 15 <> 15: no corruption, 0x820ac *)
  assert (HS : st_ok rsegs E (w10t_ssk 3 3 3 (2 ^ 47 - 4) [w10t_cNE15])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 3 3 3 (2 ^ 47 - 4) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820ac; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (w10_tail B MT cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2 L1 L2 L3); [| exact Hlen].
  rewrite Hr0 in Hc15. cbn [nth] in Hc15.
  rewrite Htie, Hr0, (w10_corr_none L c0 _ (or_introl Hc15)). exact L4. }
destruct (Z_lt_le_dec L 9) as [HL9|HL9].
{ (* len < 9: no corruption, 0x820b8 -> C2 *)
  assert (HS : st_ok rsegs E (w10t_ssk 3 3 3 (2 ^ 47 - 4) [w10t_cEQ15; w10t_cLT9])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 3 3 3 (2 ^ 47 - 4) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820c0; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  assert (Hnone : fst (corr_step L r) = None) by (rewrite Hr0; apply w10_corr_none; right; lia).
  assert (HeL : e_len (x_e cx) = L).
  { rewrite Hlen. unfold rl_len. rewrite Htie, Hnone. cbn [buf p_corr]. rewrite HW2. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_len (x_e cx))).
  { apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 40 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (w10_den_atom _ 32 _ E32). }
  assert (R24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (e_len (x_e cx))).
  { apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 40 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (w10_den_atom _ 32 _ E32). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HC2 ly2 S2). apply (w10t_mkC2 cx rest ly2 S2 W2 _ _ _ L1 L2 L3); [| exact Hlen | exact R10 | exact R24].
  rewrite Htie, Hnone. exact L4. }
pose proof Hc15 as Hc15r. rewrite Hr0 in Hc15. cbn [nth] in Hc15.
(* in.n = 3: 0x81fc4 `beq` -> RT, no byte written *)
assert (HS : st_ok rsegs E (w10t_ssk 3 3 3 (2 ^ 47 - 4) [w10t_cEQ15; w10t_cGE9; w10t_cEQ3])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
{ apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 3 3 3 (2 ^ 47 - 4) _
    HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
  all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
             | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
  (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
  (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
destruct (w10t_model_RT L c0 [xa; xb] Hc15 HL9 eq_refl) as (Hm & Hob).
apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps (8 + fst (fuzz_u16 [xa; xb]) mod (L - 8)) [] r).
apply (w10t_mkRT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HB0 L1 L2 L3 L4);
[rewrite Htie, Hr0, Hm; reflexivity | lia | unfold rs_plen; fold L; lia].
Qed.

(* ---- 1 <= |r| <= 2: c only; 0x81f80 `bltu` -> RT, no byte written ---- *)
Lemma w10t_P1_12 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r,
  rs_pre rsegs B cx -> rs_from_RT rsegs B MT cx POST rest -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_cut_P1 rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 -> (1 <= length r <= 2)%nat ->
  SRr rsegs W2 (cfg_at rsegs RS_P1 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HRT HC2 (HB & HL) Hr12.
w10t_pre HP HB HL.
pose proof (w10t_len_cell cx sh ps W2 mem2 Hwf Hpp) as HLv. unfold rs_plen in HLv.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
destruct (rs_in_now rsegs B MT cx rest rs_P0 ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl) as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof Hsuf as (jr & Hjr & Hrj).
assert (Hlr : (length r <= length rest)%nat) by (rewrite Hrj, length_skipn; lia).
set (cur := rs_cur rsegs cx rest r) in *.
assert (Hcd : cur = e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r)) by reflexivity.
assert (Hcur : 1 <= cur /\ cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (rewrite Hcd; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof (w10_build_tie rest sh np ps r Hsh Hnp Hnps Hps) as Htie.
assert (HLp : Z.of_nat (length (pod_encode (PodRec sh ps None))) = L) by (rewrite HW2; reflexivity).
rewrite HLp in Htie.
assert (HIN : forall i, (i < length r)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
  ~ (e_R (x_e cx) <= cur + Z.of_nat i < e_R (x_e cx) + 0x138) /\
  ~ (e_pp (x_e cx) <= cur + Z.of_nat i < e_pp (x_e cx) + PP_SIZE)).
{ intros i Hi. destruct (w10t_in_at cx rest r W2 mem2 i Hin Hbytes Hra Hsuf Hi) as (V & _ & N1 & N2 & _).
  split; [exact V|]. split; [exact N1 | exact N2]. }
remember (Ereg regs2 ([Z_to_bv 64 L; Z_to_bv 64 (e_F (x_e cx)); Z_to_bv 64 cur; Z_to_bv 64 (Z.of_nat (length r))]
  ++ map (fun i => Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) (seq 0 4))) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E21 : ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E27 : ew E 27 = Z_to_bv 64 (e_pp (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (e_F (x_e cx))) by (subst E; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 cur) by (subst E; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; reflexivity).
assert (EB : forall i, (i < 4)%nat -> ew E (36 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))).
{ intros i Hi. subst E. destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
assert (U27 : bv_unsigned (ew E 27) = e_pp (x_e cx)) by (rewrite E27; apply unsigned_lit_small; lia).
assert (HB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)).
assert (HAE0 : env_agree 40 E E) by apply env_agree_refl.
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 27 0 4; mkSHE 21 0 8; mkSHE 34 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 27 0 4 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 27 _ E27 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia.
  - apply (w10t_shent_in E _ 34 (e_src (x_e cx)) (e_left (x_e cx)) cur 1 Hamr HB (w10_U_atom E 34 _ E34 ltac:(lia)));
    [lia | lia | lia | exact Hra]. }
destruct (w10t_split1 r ltac:(lia)) as (c0 & r1 & Hr0).
assert (Hr1 : (length r1 <= 1)%nat) by (rewrite Hr0 in Hr12; cbn [length] in Hr12; lia).
pose proof (rm_byte_range c0) as Bc0.
unfold cfg_at. change (w64 RS_P1) with (Z_to_bv 64 0x81ed8).
destruct (Z.eq_dec (bv_unsigned (nth 0 r (Z_to_bv 8 0)) mod 16) 15) as [Hc15|Hc15].
2: { (* c & 15 <> 15: no corruption, 0x820ac *)
  assert (HS : st_ok rsegs E (w10t_ssk 1 1 2 (2 ^ 47 - 2) [w10t_cNE15])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 1 1 2 (2 ^ 47 - 2) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820ac; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (w10_tail B MT cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2 L1 L2 L3); [| exact Hlen].
  rewrite Hr0 in Hc15. cbn [nth] in Hc15.
  rewrite Htie, Hr0, (w10_corr_none L c0 _ (or_introl Hc15)). exact L4. }
destruct (Z_lt_le_dec L 9) as [HL9|HL9].
{ (* len < 9: no corruption, 0x820b8 -> C2 *)
  assert (HS : st_ok rsegs E (w10t_ssk 1 1 2 (2 ^ 47 - 2) [w10t_cEQ15; w10t_cLT9])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
  { apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 1 1 2 (2 ^ 47 - 2) _
      HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
    all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
               | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820c0; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
  destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
    (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  assert (Hnone : fst (corr_step L r) = None) by (rewrite Hr0; apply w10_corr_none; right; lia).
  assert (HeL : e_len (x_e cx) = L).
  { rewrite Hlen. unfold rl_len. rewrite Htie, Hnone. cbn [buf p_corr]. rewrite HW2. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_len (x_e cx))).
  { apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 40 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (w10_den_atom _ 32 _ E32). }
  assert (R24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (e_len (x_e cx))).
  { apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 40 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (w10_den_atom _ 32 _ E32). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HC2 ly2 S2). apply (w10t_mkC2 cx rest ly2 S2 W2 _ _ _ L1 L2 L3); [| exact Hlen | exact R10 | exact R24].
  rewrite Htie, Hnone. exact L4. }
pose proof Hc15 as Hc15r. rewrite Hr0 in Hc15. cbn [nth] in Hc15.
assert (HS : st_ok rsegs E (w10t_ssk 1 1 2 (2 ^ 47 - 2) [w10t_cEQ15; w10t_cGE9])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed8) mem2 (seg_rom rsegs)))).
{ apply (w10t_HS_lem cx rest r W2 regs2 mem2 E _ L cur (e_F (x_e cx)) 1 1 2 (2 ^ 47 - 2) _
    HE E9 E21 E23 E27 E32 E33 E34 E35 (fun i Hi => EB i ltac:(lia)) P20).
  all: first [ solve [unfold W10_HI in *; lia] | assumption | solve [intros i Hi; apply HIN; lia]
             | solve [w10t_conds EB E32 E35] | solve [vm_compute; reflexivity] ]. }
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094; [w10t_awr E (e_pp (x_e cx)) U27 Hinp Hfresh|].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 40 E E') by env_agree_chain HAE0 end.
destruct (w10t_fin_lem cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
  (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E21 E23 E27 E32 E33 HS HAE ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) ltac:(w10t_in) HFr ltac:(w10t_kwr) HJ
  (RPgCfgChanges.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
destruct (w10t_model_RT L c0 r1 Hc15 HL9 ltac:(rewrite (w10_corr_empty_tail r1 ltac:(lia)); reflexivity))
  as (Hm & Hob).
apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps (8 + fst (fuzz_u16 r1) mod (L - 8)) [] r).
apply (w10t_mkRT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HB0 L1 L2 L3 L4);
[rewrite Htie, Hr0, Hm; reflexivity | lia | unfold rs_plen; fold L; lia].
Qed.

(* ---- P1 0x81ed8: every length of what is left of the input ---- *)
Lemma w10t_P1 : forall cx POST rest,
  rs_start_M01 rsegs B cx rest -> (forall kk, rs_from_R rsegs B MT cx POST rest kk) ->
  rs_from_RT rsegs B MT cx POST rest -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_from_P1 rsegs B MT cx POST rest.
Proof.
intros cx POST rest Hst HR HRT HC2. destruct Hst as (HP & _ & _ & _).
unfold rs_from_P1. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r HP1.
destruct r as [|c0 r1].
- exact (w10t_P1_0 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps HP HC2 HP1).
- destruct (Nat.le_gt_cases (length (c0 :: r1)) 2) as [H2|H2].
  { exact (w10t_P1_12 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps _ HP HRT HC2 HP1 ltac:(cbn [length] in *; lia)). }
  destruct (Nat.eq_dec (length (c0 :: r1)) 3) as [H3|H3].
  { exact (w10t_P1_3 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps _ HP HRT HC2 HP1 H3). }
  exact (w10t_P1_4 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps _ HP HR HRT HC2 HP1 ltac:(lia)).
Qed.

(* ---- P 0x81ed4 `ld s4,0xb0(s1)`: one step to P1 ---- *)
Lemma w10t_P_step : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r,
  rs_pre rsegs B cx -> rs_from_P1 rsegs B MT cx POST rest ->
  rs_cut_P rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  SRr rsegs W2 (cfg_at rsegs RS_P regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HP1 (HB & HL).
pose proof HB as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hnps & Hps).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
unfold T_SEG_STK, ASTACK in HSTK.
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_P, rs_cur2 in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P23 & P21 & P27 & Q08 & Q10 & Q18 & Q28 & Q30 & Q68 & Q78 & Q80 & Qb0 & Qc8 & Qf8 & _).
cbn [fst snd rl_at rl_xv] in P8, P9, P19, P23, P21, P27, Q08, Q10, Q18, Q28, Q30, Q68, Q78, Q80, Qb0, Qc8, Qf8.
pose proof HC as (HJ & _).
remember (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 (e_F (x_e cx))]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E21 : ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E27 : ew E 27 = Z_to_bv 64 (e_pp (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E33 : ew E 33 = Z_to_bv 64 (e_F (x_e cx))) by (subst E; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = e_R (x_e cx)) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E (mkSS 0x81ed4 sr_atoms [w10t_rR []] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81ed4) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (w10t_rR_ok _ _ _ _ _ (e_F (x_e cx)) _ U9 E21 E23 E27 E33); try lia; try assumption. constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn. tauto. }
assert (SHOK : sh_ok rsegs W10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (HAE0 : env_agree 34 E E) by apply env_agree_refl.
unfold cfg_at. change (w64 RS_P) with (Z_to_bv 64 0x81ed4).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x81ed8.
{ awr_ok_tac. }
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ =>
  assert (HAE : env_agree 34 E E') by env_agree_chain HAE0;
  assert (HAE32 : env_agree 32 (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 (e_F (x_e cx))]) E')
    by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia) end.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn [w10t_rR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2) [Z_to_bv 5 20] HS HAE32 ltac:(vm_compute; reflexivity)) as RK.
assert (R20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (shadow_addr (e_pp (x_e cx) + 0x4000))).
{ apply (w10t_reg E _ _ ms (w_H W2) (Z_to_bv 5 20) 34 w10t_sh21 _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  exact (w10_den_sh _ 21 23 _ E21 ltac:(lia) E23). }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (HP1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh np ps r).
split.
- split; [|split; [|split]].
  + apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    * intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    * apply RPgCfgChanges.same_io_wvb.
    * intros a Ha _. exact (HK a Ha).
    * intros a [].
  + apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
    intros i Hi. apply HK. change (length rs_P0) with 52%nat in Hi.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)).
    assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  + apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_pp (x_e cx)) _ Hpp).
    intros x Hx. apply HK. destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
    assert (HLI : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
    { unfold pc_image. apply length_pp_image; [unfold POD_BUF_MAX in *; lia | |].
      - rewrite (pc_ents_final sh ps None). exact HW3.
      - rewrite (pc_ents_final sh ps None). exact HW4. }
    try (unfold rs_u8s in Hx; rewrite length_map in Hx). rewrite HLI in Hx. unfold PP_SIZE in Hx. lia.
  + exact (conj Hin (conj Hsuf (conj Hwf (conj Hlen (conj Hsh (conj Hnp (conj Hnps Hps))))))).
- unfold rs_at_cx, rs_at. apply Forall_app. split.
  + apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
    intros f Hf. unfold rs_L_P, rs_cur2 in Hf. cbv zeta in Hf. cbn [app] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
      first [ solve [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]]
            | solve [intros i Hi; apply HK; lia] ] |]).
    destruct Hf.
  + apply Forall_cons; [exact R20 | apply Forall_nil].
Qed.

(* ---- the piece: RPgSeg.rs_piece_W10_post_stmt ---- *)
Theorem w10_post : rs_piece_W10_post_stmt rsegs B MT.
Proof.
unfold rs_piece_W10_post_stmt. intros cx POST rest Hst HR HRT HC2.
pose proof (w10t_P1 cx POST rest Hst HR HRT HC2) as HP1.
split; [|exact HP1].
unfold rs_from_P. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r HcP.
destruct Hst as (HP & _).
exact (w10t_P_step cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HP1 HcP).
Qed.
End t.

Print Assumptions w10_post.
