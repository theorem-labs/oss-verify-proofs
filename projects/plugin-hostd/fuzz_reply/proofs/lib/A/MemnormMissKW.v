(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormMissKW.v (commit 3295f3a9fd5, CfInstMiss lane M field round 3 (cf-miss 3295f3a9fd5); file sha256 1709a8e0ff9d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 8 image addresses moved by function pairs the comparison kit cmpkit 4bbd3a74be89 calls the same code except at the by-hand acceptances named below (strictcmp2 16982e3ef42b, by funcpair_reply 053b61532a33 on the cgif twin ce511d541cda; 8 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance of the kit's known false-difference class (accept.tsv, re-measured each run: the bytes the code reads equal and read-only on both images): _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb+0xdc); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane for a Theorem Labs lane, lane missw): MemnormMissKW, the AIfaceMw variant of MemnormMissK.v (c5
   8d6c9f45705b): the refill's stack window is the Section variable RW (0 <= RW, 176 + RW <= AFSTACK: hypothesis
   RWB) of MnRefillW.v, not RSTACK = 1024.  Same proof script; the changes are AIfaceM -> AIfaceMw (fields if_ ->
   ifw_), the refill leaves -> their _w forms at RW, RSTACK -> RW, the refill-window steps through
   MnRefillW.win_af_w and the other frame lia steps under RWB, RW (and RWB) in the explicit arguments of the W
   twins' lemmas, and the imports of the W twins.  MemnormMissK.v is unchanged.  rule 24: no function proved (kind:
   re-statement of a proved miss walk over a wider refill window). *)
(* Theorem Labs, 2026-10 (task MEMNORM): the memnorm-kept twin of the k-path MISS arm at can_fill = 1.
   [alloc_missk_em] is AGinW.alloc_missk_e with MemnormT.alloc_leaf_em (ErrnoG.alloc_leaf_e plus
   `memnorm mem -> memnorm mem'`) in place of ErrnoG.alloc_leaf_e.
   rule 24: no function proved (kind: arm twin, frame corollary over the refill's memnorm-kept contract).

   AGin's Section variables and hypotheses in AGin's order, with the refill's add-on IFME replaced by the refill's
   memnorm-kept contract [RFm] (MnRefillW.amm_refill_w_t).  No new walking: every step is AGin's lemma, cited.
   The keep is the chain of the arm's own raw frames and the refill's keep:
   - MISS1's raw frame MEQW (outside AGj8.WINM: Allocate's stack window and the thread's unwinding byte;
     [memnorm_winm_k]);
   - the refill's keep (rleaf_em);
   - the grant path (a0 = 1): at_RETkw's raw frame MEQF at the post-refill layout (MemnormHitK.memnorm_at_RETkw);
   - the class-full OOM path (a0 = 0): the OOM run's raw frame (AGj9.at_RETN: outside AGj9.WINN, i.e. the stack
     window, the OOM flag byte and errno; MemnormMissGW.memnorm_winn).
   Copied (marked): AGin's REFILL_e / JOIN_e / OOMJ_e / missk_core_e / alloc_missk_e scripts, each over the _em lemmas.
   AGin and every existing statement are unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFhy AFhm AGhy AFi1 AGhz AGi2 AGi4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGj6 AFi3 AllocG AGif0n AGif2reply AGif0reply AGjc AGjd AGje AGjb AGjg AGja AGj8 AGj7 AGj9 AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ErrnoG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoApart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MnRefillW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGinW AGk1EW ImgBaseAG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT MemnormHitG MemnormHitK MemnormLocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormMissGW.
(* field round 3: the read-only data predicate at Allocate's entry, used qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames YG0dcf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
(* copy of AGin.v:37 *)
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg}.
Local Open Scope am_scope.

(* MISS1's window on the k path (AGj8.WINM): Allocate's stack window and the thread's unwinding byte. *)
Lemma memnorm_winm_k : forall ly (regs0 : bvmap 5 word) (mem0 m : word -> option byte), layout_ok ly -> img_cover ly ->
  ly_stk_lo ly + AGhy.AFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
  (forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> m x = mem0 x) -> MemnormT.memnorm_keep tfibsegs mem0 m.
Proof.
intros ly regs0 mem0 m LY IMG Hlo Hhi F.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (MemnormLocG.memnorm_keep_window tfibsegs (AGj8.WINM ly regs0) mem0 m); [|exact F].
intros x Hw. unfold AGj8.WINM in Hw. cbv zeta in Hw. destruct Hw as [Hw|Hw].
- apply MemnormHitG.mn_safe_high. unfold AGhy.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- apply (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
    ltac:(unfold owned_extents; right; right; left; reflexivity)).
  cbn [fst snd]. unfold t_unwinding, kThreadObjSize in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* copy of AGin.v:119-132, 139 (AGin's section b), with the refill's memnorm-kept contract in place of IFME *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
Variable rtree : Z -> M unit.
Variable RW : Z.
Hypothesis RWB : 0 <= RW /\ 176 + RW <= AFSTACK.
Hypothesis IFM : MnRefillW.AIfaceMw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW.
(* The refill callee with errno and memnorm kept (MnRefillW.amm_refill_w_t), in place of AGin's IFME. *)
Hypothesis RFm : MnRefillW.amm_refill_w_t B ARX AOX rpre lpost rtree RW.
(* copy of AGin.v:157-159 (the image facts AGinW.LEAFJ_e reads) *)
Hypothesis EAI : ErrnoApart.errno_in_img.
Hypothesis EAS : ErrnoApart.errno_apart_shadow_ag.
Hypothesis EAD : ErrnoApart.errno_apart_dzone_ag.
(* AGin's section-b definitions. *)
Local Abbreviation Finst := (AGinW.Finst B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF).
Local Abbreviation if_mview := (AGinW.if_mview B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM).
Local Abbreviation if_shape_miss := (AGinW.if_shape_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM).
Local Abbreviation vregs := AGinW.vregs.
Local Abbreviation vregs_other := AGinW.vregs_other.
Local Abbreviation vregs_10 := AGinW.vregs_10.
Local Abbreviation vregs_11 := AGinW.vregs_11.
Local Abbreviation vregs_12 := AGinW.vregs_12.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* copy of AGin.v:206-244 (AGin's section c) *)
Section c.
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Hypothesis Hnnmax : n < nmax.
Hypothesis HBB : blocks_bytes S + n <= lmax.
Hypothesis Htr : U tr S.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let cl : Z := chunk_class n.
Let csz : Z := class_size cl.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hcf1 : getr regs0 15 = w64 1.
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis PSO : val_mem tfibsegs (mrestrict (w_H W) mem0) SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs (mrestrict (w_H W) mem0) (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
(* field round 3: the refill's call-state facts at the entry memory (AbudgetRestate's lane text) *)
Hypothesis HRO0 : YG0dcf.arodata_ok_cf tfibsegs B mem0.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.
(* AGin's section-c facts. *)
Local Abbreviation Hn0 := (@AGinW.Hn0 ly regs0 n tr Nrange Htrlen).
Local Abbreviation FP := (@AGinW.FP n Nrange).
Local Abbreviation Hcl := (@AGinW.Hcl ly regs0 n tr Nrange Htrlen).
Local Abbreviation LY := (AGinW.LY B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen).
Local Abbreviation IMG := (AGinW.IMG B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen).
Lemma Hcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Let E0m : env := AGj6.E0 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0.
Local Abbreviation MISS1 := (AGinW.MISS1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW IFM inst ly S W regs0 regsU mem0 md0 n tr
  HARX Nrange Hmiss Htrlen Hn Hi11 Htp Hsp Hso Hbp Hcf1 Hpres0 PSO PLEN PBUF0 HUo HU10 HU11 HU12 HU14).
Local Abbreviation ms1_shape := (AGinW.ms1_shape W).
Local Abbreviation RAZ1 := (AGinW.RAZ1 ly W regs0 n tr Htrlen).
Local Abbreviation PL_e := (AGinW.PL_e B mt ARX AOX lpost inst ly S W regsU mem0 md0 n tr).
(* AGinW.PL_e over alloc_leaf_em (MemnormMissGW.PL_em: the same pre-leaf). *)
Local Abbreviation PL_em := (MemnormMissGW.PL_em B mt ARX AOX lpost inst ly S W regsU mem0 md0 n tr).

(* --- The refill-call machine state (copy of AGin.v:330-336). --- *)
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
(* AGin's section-f facts. *)
Local Abbreviation AG1 := (AGinW.AG1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange Hmiss Htrlen ms1 Em HEm HSC MEQW).
Local Abbreviation SP1 := (AGinW.SP1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC).
Local Abbreviation R_ra := (AGinW.R_ra W ms1 Em HSC).
Local Abbreviation R_gp := (AGinW.R_gp ly W regs0 n tr Htrlen ms1 Em HEm HSC).
Local Abbreviation R_tp := (AGinW.R_tp W ms1 Em HSC).
Local Abbreviation R_a0 := (AGinW.R_a0 ly W regs0 n tr Htrlen ms1 Em HEm HSC).
Local Abbreviation R_a1 := (AGinW.R_a1 ly W regs0 n tr Htrlen ms1 Em HEm HSC).
Local Abbreviation R_a2 := (AGinW.R_a2 inst ly W regs0 n tr Htrlen Hi11 ms1 Em HEm HSC).
Local Abbreviation R_a3 := (AGinW.R_a3 ly W regs0 n tr Htrlen ms1 Em HEm HSC).
(* MISS1's raw frame keeps memnorm (memnorm_winm_k). *)
Lemma MNW : MemnormT.memnorm_keep tfibsegs mem0 (ms_mem ms1).
Proof. pose proof Hsp as (Hlo & _ & Hhi & _). exact (memnorm_winm_k ly regs0 mem0 (ms_mem ms1) LY IMG Hlo Hhi MEQW). Qed.
(* The refill call: AGinW.REFILL_e's premises, over RFm (the post rleaf_em keeps errno and memnorm). *)
Lemma REFILL_em : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
  (MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1)).
Proof.
(* copy of AGin.v:392-397, over RFm *)
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
assert (RAW : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) ->
  ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) -> ms_mem ms1 x = mem0 x).
{ intros x N1 N2. apply MEQW. unfold AGj8.WINM. intros [X|X]; [exact (N1 X) | exact (N2 X)]. }
exact (RFm inst ly S W mem0 md0 n sp0 (ms_regs ms1) (ms_mem ms1) mat1 HARX HRP HRO0 Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW PRESW
  SP1 R_ra (eq_trans R_gp Hgp) R_tp R_a0 R_a1 R_a2 R_a3).
Qed.

(* --- After the refill (copy of AGin.v:402-418), with the refill's keep. --- *)
Section g0.
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis CIp : st_cache_inited S' = true.
Hypothesis HBBp : blocks_bytes S' = blocks_bytes S.
Hypothesis HDPp : st_depot S' = st_depot S.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HAREGS : aregs_preserved (ms_regs ms1) regsR.
Hypothesis HSIO : same_io (md0' mat1) mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ (ms_regs ms1) - RW <= a < spZ (ms_regs ms1)) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ (ms_regs ms1) - RW <= bv_unsigned x < spZ (ms_regs ms1)) -> memR x = (ms_mem ms1) x.
Hypothesis HPRR : forall a, spZ (ms_regs ms1) - RW <= a < spZ (ms_regs ms1) -> apresent (w_H W') memR a.
(* ERRNO-KEPT: the refill keeps errno (MnRefillW.rleaf_e_w RW); used only by the _e lemmas. *)
Hypothesis HERRp : ErrnoG.errno_kept B (ms_mem ms1) memR.
(* the refill's keep (rleaf_em) *)
Hypothesis HMN : MemnormT.memnorm_keep tfibsegs (ms_mem ms1) memR.
(* copy of AGin.v:419-420 *)
Let msR : machine_state := mkst regsR (w64 0x36528) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Local Abbreviation Hsp' := (@AGinW.Hsp' ly S regs0 Hsp ly' Hly).
(* memnorm from the entry memory to the refill's return: MISS1's raw frame MEQW, then the refill's keep. *)
Lemma MN1 : MemnormT.memnorm_keep tfibsegs mem0 memR.
Proof. exact (MemnormLocG.memnorm_keep_trans _ _ _ _ MNW HMN). Qed.

(* --- The a0 = 1 cache join (copy of AGin.v:500-506). --- *)
Section g.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA1 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly' S' W' tr z m.
Local Abbreviation HV' := (AGinW.HV' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation LY' := (AGinW.LY' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation IMG' := (AGinW.IMG' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hv' := (AGinW.Hv' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
(* AGinW.TAILJ (the remaining arguments are the join state's junk values). *)
Local Abbreviation TAILJ := (AGinW.TAILJ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW RWB IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange Hmiss Htr Htrlen Hn Hi11 Htp Hgp Hra Hsp Hso Hbp Hcf1 PSO PLEN ms1 Em HEm HSC MEQW PRESW BUFW
  S' ly' W' regsR memR mdR HARXp CIp HDPp Hly HAREGS HFRA HPRR l off Hcache' HA1).
(* AGinW.LEAFJ_e (the remaining arguments are the junk byte of the join state and the result). *)
Local Abbreviation LEAFJ_e := (AGinW.LEAFJ_e B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW RWB IFM EAI EAS EAD inst ly S W regs0 regsU mem0 md0 n tr
  HARX HRP Nrange Hmiss Hnnmax HBB Htr Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW
  S' ly' W' memR mdR HARXp CIp HBBp Hly HWLE HSIO HFRA HFRR HPRR HERRp l off Hcache').

Section gj.
Variables (jb : Z).
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (AGj6.Kv ly' cl v' + AGj6.RZ - 15) 1 jb.
(* AGinW.LEAFJ_e with memnorm kept: MN1, then at_RETkw's raw frame MEQF at the post-refill layout
   (MemnormHitK.memnorm_at_RETkw). *)
Lemma LEAFJ_em : forall r W'' c'',
(exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\ (odd = true <-> AGj6.NPv n mod 8 <> 0) /\
  AGif0n.at_RETkw W' ly' regs0 memR mdR n cl cnt' v' jb DPOST' odd z W'' c'') -> PL_em r W'' c''.
Proof.
intros r W'' c'' H HPATH.
apply MemnormMissGW.alloc_leaf_em_of_e; [exact (LEAFJ_e jb Hjb Hjb_def r W'' c'' H HPATH)|].
intros regs1 mem1 md1 Hc.
destruct H as (odd & z & _ & _ & HR).
destruct HR as (_ & regs' & mem' & mat & Hc' & _ & _ & _ & MEQF & _).
assert (EQM : mem' = mem1).
{ rewrite Hc' in Hc. unfold cfg_at in Hc. exact (f_equal (fun c => ms_mem (cfg_ms c)) Hc). }
subst mem1.
pose proof Hsp' as (Lo' & _ & Hi' & _).
exact (MemnormLocG.memnorm_keep_trans _ _ _ _ MN1
  (MemnormHitK.memnorm_at_RETkw ly' regs0 n cl v' odd memR mem' LY' IMG' Lo' Hi' Hcl (proj1 Hv') (proj2 Hv') Nrange MEQF)).
Qed.
End gj.

(* AGinW.JOIN_e over LEAFJ_em. *)
Lemma JOIN_em : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36528 regsR memR mdR) PL_em.
Proof.
(* copy of AGin.v:761-764 *)
destruct (@AGjd.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ; eassumption].
intros r W'' c'' H. eapply LEAFJ_em; eassumption.
Qed.
End g.

(* --- The a0 = 0 class-full OOM arm (AGin's section h). --- *)
Section h.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Local Abbreviation segN_run := (AGinW.segN_run B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW RWB IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange Hmiss Htrlen Htp Hra Hsp Hso Hbp ms1 Em HEm HSC PRESW S' ly' W' regsR memR mdR HARXp Hly HAREGS HFRA HPRR Hc0 HA0).
Local Abbreviation LEAFN := (AGinW.LEAFN B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW RWB IFM inst ly S W regs0 regsU mem0 md0 n tr
  HARX Nrange Hmiss Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW S' ly' W' memR mdR HARXp HLPp Hly HWLE HSIO HFRA HFRR HPRR Hc0).
(* AGinW.OOMJ_e with memnorm kept: MN1, then the OOM run's raw frame (AGj9.at_RETN, outside AGj9.WINN). *)
Lemma OOMJ_em : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36528 regsR memR mdR) PL_em.
Proof.
(* copy of AGin.v:873-876 *)
unfold malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K_t. cbn [amreal].
replace (cfg_at tfibsegs 0x36528 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono; [exact segN_run|]. intros W6 c6 _ HR HPATH.
apply MemnormMissGW.alloc_leaf_em_of_e.
- exact (AGk1EW.alloc_leaf_e_null tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr (PNull, S') W6 c6 eq_refl
    (LEAFN W6 c6 HR HPATH)).
- intros regs1 mem1 md1 Hc. pose proof HR as (_ & regsx & memx & matx & Hcx & _ & _ & FRN & _ & _).
  assert (EQM : memx = mem1).
  { rewrite Hcx in Hc. unfold cfg_at in Hc. exact (f_equal (fun c => ms_mem (cfg_ms c)) Hc). }
  subst mem1. pose proof Hsp as (Hlo & _ & Hhi & _).
  assert (HWN : forall a, AGj9.WINN regs0 a -> (sp0 - AFSTACK <= a < sp0) \/
    (TFIB_OOM <= a < TFIB_OOM + 1) \/ (TFIB_ERRNO <= a < TFIB_ERRNO + 4))
    by (intros a X; unfold AGj9.WINN in X; cbv zeta in X; unfold sp0; lia).
  exact (MemnormLocG.memnorm_keep_trans _ _ _ _ MN1
    (MemnormMissGW.memnorm_winn ly sp0 (AGj9.WINN regs0) memR memx LY Hlo Hhi HWN FRN)).
Qed.
End h.
End g0.
End f.

(* AGinW.missk_core_e over alloc_leaf_em: the refill through REFILL_em (rleaf_em), the branches through OOMJ_em /
   JOIN_em. *)
Lemma missk_core_em : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
(* copy of AGin.v:930-965, over the _em lemmas *)
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_em).
{
rewrite (if_shape_miss n tr S Hn0 FP Hmiss). fold cl.
eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
change (set_nev (st_nev S + 1) S) with S1.
eapply (YG0d.amreal_mbind tfibsegs (rtree cl) (fun _ : unit => malloc_join_t stag n tr cl) S1 W _
(fun r W1 c1 => exists ms1 mat1 Em,
  ((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1) /\
   (forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
   (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
   (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
  MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x369c8) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL_em; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & HDPp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HERRp & HMN & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x36528) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ_em; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN_em; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_em CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The theorem: AGinW.alloc_missk_e concluding alloc_leaf_em. *)
Theorem alloc_missk_em : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31bd8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGin.v:1030-1073, over missk_core_em *)
intros inst so bp ly S W regs mem md n tr PRE HRO Nrange Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply AGinW.FP; eassumption).
pose proof (if_mview inst ly S W mem md n HARX ltac:(lia) FP0 Hmiss) as HMV0.
pose proof (lo_top ly (AGif0n.mv_ly B W ly inst mem (chunk_class n) HMV0)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
set (regs0 := vregs regs n inst bp).
assert (Hso64 : 0 <= so < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
assert (HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs r = getr regs0 r)
by (intros r H10 H11 H12; unfold regs0; symmetry; exact (vregs_other regs n inst bp r H10 H11 H12)).
assert (HU10 : getr regs 10%bv = getr regs0 11%bv) by (unfold regs0; rewrite Hr10, vregs_11; reflexivity).
assert (HU11 : getr regs 11%bv = getr regs0 10%bv) by (unfold regs0; rewrite Hr11, vregs_10; reflexivity).
assert (HU12 : getr regs 12%bv = w64 8) by exact Hr12.
assert (HU14 : getr regs 14%bv = w64 1) by exact Hr14.
assert (Hn : getr regs0 10 = w64 n) by (unfold regs0; apply vregs_10).
assert (Hi11 : getr regs0 11 = w64 inst) by (unfold regs0; apply vregs_11).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply vregs_other; bvne).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply vregs_other; bvne).
assert (R12 : bv_unsigned (getr regs0 12) = bp) by (unfold regs0; rewrite vregs_12; apply w64_unsigned; exact Hbp64).
assert (R13 : bv_unsigned (getr regs0 13) = so)
by (unfold regs0; rewrite (vregs_other regs n inst bp 13%bv) by bvne; rewrite Hr13; apply w64_unsigned; exact Hso64).
assert (Htp0 : getr regs0 4 = w64 TFIB_TP) by (unfold regs0; rewrite (vregs_other regs n inst bp 4%bv) by bvne; exact Htp).
assert (Hgp0 : getr regs0 3 = w64 (as_gp B)) by (unfold regs0; rewrite (vregs_other regs n inst bp 3%bv) by bvne; exact Hgp).
assert (Hcf1 : getr regs0 15 = w64 1) by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; exact Hr15).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
change (cfg_at tfibsegs 0x31bd8 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missk_core_em inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
End b.
End a.
