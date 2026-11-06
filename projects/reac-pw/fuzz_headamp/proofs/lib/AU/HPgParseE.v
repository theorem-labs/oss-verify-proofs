(* reac_headamp_prop_parse_result 0x849ac of reac-pw/fuzz_headamp's image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): segment E of its walk, lib/AU/HPgParseCut.v's
   segE_stmt. Proves function reac_headamp_prop_parse_result (this file: its first segment).

   The walk of 0x849ac .. the cuts EPI 0x84b38 and FIND 0x84bc4, in four engine chunks and one instruction by hand:

   A  0x849ac .. 0x849e4   `addi sp,sp,-0x100` and the thirteen `sd` into [sp0 - 104, sp0); the saved words come back
                           out of the stack region's chunks as the values hp_saved_ok asks for.
   .  0x849e4              `fsd fs0,0x90(sp)`, stepped by lib/A/HPgParseGPro.v's hgp_fsd.
   B  0x849e8 .. 0x84a64   `addi s0,sp,0x100`, `andi sp,sp,-0x20`, s1/s2/s3 = res/cap/out, the .got word 0x9c7f0 and
                           the shadow-offset cell 0xa5238, the three frame header words at spa + 64, +72, +80, and the
                           hole's eight `sb` at s10; two aliases name spa and shadow_addr (spa + 0x40), and the run is
                           the non-token one (the hole's write window lies inside the shadow span).
   Chunks A, the fsd and B are lib/A/HPgParseE.v's hpe_entry (image A, 0x845b4) at image B's pcs and literals.
   C  0x84a64 .. 0x84ab4   `beqz s1` (res = 0: nothing is written) and the three `sw zero` at res, res + 4, res + 8,
                           each after its instrumented check; res's range is addressable (hd_parse_args), so the
                           checks pass, and the branch on res & 3 (0x84a6c) is not taken (res mod 4 = 0).
   D  0x84ab4 .. the cut   `li s4,-1`, `beqz a0` (NULL -> EPI, rc -1); the pod's three header words, each loaded after
                           its instrumented check (the pod's range is addressable), the branch on a0 & 3 (0x84ac0)
                           not taken (P mod 16 = 0); the tests 0x84adc `bnez (size >> 20)`, 0x84af8 `bltu size,8`,
                           0x84b04 `bne type,15`, 0x84b28 `bne object type,0x40002` -> EPI (rc -1), 0x84b30
                           `bgeu size,16`: below 16, 0x84b34 `li s4,0` -> EPI (rc 0), else the find setup
                           0x84bac .. 0x84bc0 -> FIND 0x84bc4 at r = 16. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGKit HPgParseGWalk HPgParseGPro HPgParseGHdr.

Local Notation pctx := (@hp_ctx rsegs).

(* ======================================= the pcs of this segment ======================================= *)
Definition PC_RES : Z := 0x84a64.          (* after the hole is open: `beqz s1` *)
Definition PC_HDR : Z := 0x84ab4.          (* res written (or res = 0): `li s4,-1` *)

(* the image-independent model facts, engine forms and region lemmas are lib/A/HPgParseGHdr.v's hgh_* *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.

Local Notation ctx := (hp_ctx (segs := rsegs)).

(* ---------------------------------- the two cut states of this segment ---------------------------------- *)
(* what holds at 0x84a64, the first pc after the hole is open: everything hp_core asks for but res's bytes
   (the three `sw zero` have not run yet) *)
Definition pbE_core0 (x : ctx) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem md (hx_k x) (hx_fr x) PAT_KEY /\
same_io (hx_mdc x) md /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
 hx_view x mem a = hx_view x (hx_memc x) a) /\
hp_saved_ok x mem /\
(exists ev', rd32 (hx_view x mem) (as_errno B) ev') /\
(hx_R x <> 0 -> forall a, hx_R x <= a < hx_R x + 12 -> apresent (w_H (hx_W x)) mem a) /\
getr regs 2 = w64 (hx_spa x) /\ getr regs 8 = w64 (hx_sp x) /\
getr regs 3 = getr (hx_regs x) 3 /\ getr regs 4 = getr (hx_regs x) 4 /\
getr regs 9 = w64 (hx_R x) /\ getr regs 18 = w64 (hx_cap x) /\ getr regs 19 = w64 (hx_O x) /\
getr regs 26 = w64 (hx_shf x) /\ getr regs 27 = w64 SHADOW_OFF.

Definition pbE_a0 (x : ctx) (regs : bvmap 5 word) : Prop :=
getr regs 10 = w64 (if hx_null x =? 0 then hx_P x else 0).

(* 0x84a64 *)
Definition pbE_pre (x : ctx) (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
pbE_core0 x regs mem md /\ hp_fx F fc /\ pbE_a0 x regs.

(* 0x84ab4: res holds its three zero words (or res = 0) *)
Definition pbE_hdr (x : ctx) (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md /\ hp_fx F fc /\ pbE_a0 x regs.

(* ---------------------------------- repacking hp_core ---------------------------------- *)
(* the registers hp_core names, as one predicate *)
Definition pbE_cregs (x : ctx) (regs : bvmap 5 word) : Prop :=
getr regs 2 = w64 (hx_spa x) /\ getr regs 8 = w64 (hx_sp x) /\
getr regs 3 = getr (hx_regs x) 3 /\ getr regs 4 = getr (hx_regs x) 4 /\
getr regs 9 = w64 (hx_R x) /\ getr regs 18 = w64 (hx_cap x) /\ getr regs 19 = w64 (hx_O x) /\
getr regs 26 = w64 (hx_shf x) /\ getr regs 27 = w64 SHADOW_OFF.

Lemma pbE_cregs_of_core0 : forall x regs mem md, pbE_core0 x regs mem md -> pbE_cregs x regs.
Proof.
intros x regs mem md (_ & _ & _ & _ & _ & _ & H2 & H8 & H3 & H4 & H9 & H18 & H19 & H26 & H27).
repeat split; assumption.
Qed.

(* ---------------------------------- the NULL first argument ---------------------------------- *)
Definition pbE_ss_null : sstate :=
mkSS PC_HDR (sr_set sr_atoms (10%bv : bv 5) (SLit 0)) [] None (mkFacts [] [] []).

Lemma pbE_entry_null : forall (x : ctx) (F : bvmap 5 word) (fc : bv 32) regs mem,
getr regs 10 = w64 0 ->
st_ok (fx := mkFP F fc) rsegs (Ereg regs []) pbE_ss_null
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_HDR) mem (seg_rom rsegs))).
Proof.
intros x F fc regs mem H10.
rewrite restrict_mkst_fx. unfold pbE_ss_null.
apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | |].
  + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
  + rewrite H10. reflexivity.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Lemma pbE_hdr_null : forall (x : ctx), EPI_ok B MT x -> hx_null x = 1 ->
forall F fc regs mem md, pbE_hdr x F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_HDR regs mem md) (PPOST B MT x).
Proof.
intros x HE Hnull F fc regs mem md (HC & HFX & Ha0).
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
assert (H10 : getr regs 10 = w64 0)
by (unfold pbE_a0 in Ha0; rewrite Hnull in Ha0; exact Ha0).
pose proof (pbE_entry_null x F fc regs mem H10) as HS.
pose proof HC as (HJ & Hio & HK & HSV & HO & HR & HEv & _).
pose proof (hk_core_cregs B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md HC) as HCR.
pose proof HJ as (HAJ & HST & HPAT).
unfold cfg_at. change (w64 PC_HDR) with (Z_to_bv 64 PC_HDR).
aj_run_toH pb_tbl_ok HS HAJ PC_EPI.
{ apply awr_okH_nil. }
lazymatch goal with HF : frame_of _ _ _ (ms_mem ?msn) |- _ =>
  assert (Hm : ms_mem msn = mem)
  by (apply functional_extensionality; intros w; apply HF; intros (r & Hin & _); destruct Hin) end.
rewrite Hm in *.
lazymatch goal with HS2 : st_ok _ _ _ (restrict _ ?msn) |- _ =>
  pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ msn HS2 eq_refl) as Hshape;
  rreg HS2 (20%bv : bv 5) R20;
  pose proof (regs_kept_of_st_ok rsegs _ _ (restrict (w_H (hx_W x)) msn) regs (@nil word)
    [2; 3; 4; 8; 9; 18; 19; 26; 27]%bv HS2 (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR
end.
cbn [ms_regs restrict] in HKR.
rewrite Hshape.
lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md2) ?Q =>
  change (SRr s W (cfg_at (fx := mkFP F fc) rsegs PC_EPI rg mm md2) Q) end.
apply (HE F fc).
rewrite Hm. unfold EPI_at. rewrite (hgh_ans_null x Hnull).
cbn [ans_cells ans_res_bytes ans_rc ans_n ans_keys ans_rf fst snd].
split; [|split; [exact HFX|]].
- apply (hgh_core_mk B).
  + split; [exact HAJ | split; [exact HST | exact HPAT]].
  + hgh_io.
  + exact HK.
  + exact HSV.
  + apply hgh_garr8_nil.
  + exact HR.
  + exact HEv.
  + eapply hk_cregs_same; solve [exact HCR | apply HKR; cbv [In]; tauto].
- rewrite R20. apply bv_eq. vm_compute. reflexivity.
Qed.

End b.

(* the pod's header as a read-only region at a0 (atom 10): the u32 at 0, 4 and (when 16 bytes are there) 8 *)
Definition pbE_pod_rg (big : bool) : YP09.region :=
if big then YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 47 0)); YP09.mkChunk 4 (CVal 4 (SOff 48 0)); YP09.mkChunk 8 (CVal 4 (SOff 49 0))]
else YP09.mkRegion (Some 10%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 47 0)); YP09.mkChunk 4 (CVal 4 (SOff 48 0))].
Definition pbE_hdr_atoms : list (nat * afact) :=
hk_atoms ++ [(10%nat, mkAF 16 (2 ^ 47 - 16) 4);
  (47%nat, mkAF 0 (2 ^ 32 - 1) 0); (48%nat, mkAF 0 (2 ^ 32 - 1) 0); (49%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition pbE_ss_hdr (big : bool) : sstate :=
mkSS PC_HDR sr_atoms [pbE_pod_rg big] None (mkFacts pbE_hdr_atoms [] []).
Definition pbE_SH (big : bool) : list shent := [mkSHE 10%nat 0 (if big then 16 else 8)].

(* res [R, R + 12) as a writable region at s1 (atom 9); on the NULL-res arm s1 is pinned to 0 *)
Definition pbE_res_rg : YP09.region := YP09.mkRegion (Some 9%nat) 0 12 0 12 [].
Definition pbE_res_atoms : list (nat * afact) := hk_atoms ++ [(9%nat, mkAF 4 (2 ^ 47 - 12) 2)].
Definition pbE_ss_res : sstate := mkSS PC_RES sr_atoms [pbE_res_rg] None (mkFacts pbE_res_atoms [] []).
Definition pbE_SH_res : list shent := [mkSHE 9%nat 0 12].
Definition pbE_ss_res0 : sstate :=
mkSS PC_RES (sr_set sr_atoms (9%bv : bv 5) (SLit 0)) [] None (mkFacts [] [] []).

(* the write-set obligation of a run whose regions are all read-only *)
Ltac pbE_awr_ro :=
idtac; lazymatch goal with |- awr_okH ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?U =>
let rs' := eval vm_compute in rs in change (awr_okH E rs' stk sp0 fp b0 bc ly own U);
repeat first
[ apply awr_okH_nil
| apply awr_okH_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ] end.

(* a run whose regions have empty write windows leaves the memory as it was *)
Ltac pbE_nowrange :=
intros (r & Hin & Hb); cbv [ss_mem pbE_ss_hdr pbE_pod_rg] in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<-|Hin];
  [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hb; lia|]);
destruct Hin.
Ltac pbE_mem_eq mem Hm :=
lazymatch goal with HF : frame_of _ _ _ (ms_mem ?msn) |- _ =>
  assert (Hm : ms_mem msn = mem)
  by (apply functional_extensionality; intros wm;
      repeat lazymatch goal with
      | HG : frame_of _ _ ?a (ms_mem ?m1) |- ms_mem ?m1 wm = mem wm =>
          rewrite (HG wm ltac:(pbE_nowrange))
      end; reflexivity) end.

(* a register at a stop, as the engine's symbolic value [RPgParseE.v pe_reg] *)
Ltac pbE_reg HS r Q :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS)
end.

(* the engine's three steps, with this walk's table, shadow base and span *)
Ltac pbE_run :=
lazymatch goal with
| HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tokH pb_tbl_ok HS HJ SHOK hk_Bspan end.
Ltac pbE_run_to stop :=
lazymatch goal with
| HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tokH pb_tbl_ok HS HJ SHOK hk_Bspan stop end.
Ltac pbE_branch Hc :=
lazymatch goal with
| HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pb_tbl_ok HS SHOK hk_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

(* ======================================= the three chunks' pcs ======================================= *)
Definition PF_FSD : Z := 0x849e4.      (* fsd fs0,144(sp) *)
Definition PF_B : Z := 0x849e8.        (* addi s0,sp,256 *)

(* ======================================= chunk A ======================================= *)
(* the parse's whole stack window [sp0 - 0x120, sp0) *)
Definition pbA_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-0x120) 0 (-0x120) 0 [].
Definition ss_pbA : sstate :=
mkSS B_PARSE_RESULT sr_atoms [pbA_stk] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

(* ======================================= chunk B ======================================= *)
(* slot 32 = SHADOW_OFF, slot 33 = spa, slot 34 = the hole's first shadow byte *)
Definition pbB_fr : YP09.region := YP09.mkRegion (Some 33%nat) 64 88 64 88 [].
Definition pbB_hole : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 8 [].
Definition pbB_got : YP09.region :=
YP09.mkRegion None PB_GOT_SH (PB_GOT_SH + 8) 0 0 [YP09.mkChunk PB_GOT_SH (CVal 8 (SLit PB_SH_CELL))].
Definition pbB_cell : YP09.region :=
YP09.mkRegion None PB_SH_CELL (PB_SH_CELL + 8) 0 0 [YP09.mkChunk PB_SH_CELL (CVal 8 (SOff 32 0))].
(* `andi sp,sp,-0x20` and `add s10,(sp + 0x40) >> 3,s11` are the two aliases the engine needs *)
Definition pbB_al1 : sv * sv := (SAlu ALU_AND (SOff 2 0) (SLit (-32)), SOff 33 0).
Definition pbB_al2 : sv * sv :=
(SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 64) (SLit 3)) (SOff 32 0), SOff 34 0).
Definition pbB_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
         (33%nat, mkAF (2 ^ 46 - 288) (2 ^ 47) 5);
         (34%nat, mkAF (SHADOW_OFF + 2 ^ 43) (SHADOW_OFF + 2 ^ 44) 2)] [] [pbB_al1; pbB_al2].
Definition ss_pbB : sstate := mkSS PF_B sr_atoms [pbB_fr; pbB_hole; pbB_got; pbB_cell] None pbB_facts.

(* a one-byte chunk holding a literal, read through the view *)
Lemma pbF_chunk_byte : forall E (H : word -> bool) (mem : word -> option byte) base off v,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal 1 (SLit v))) ->
aview rsegs H mem (base + off) = Some (zcanon v mod 256).
Proof.
intros E H mem base off v HC.
destruct (HC 0 ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val cbyte byte_of_word] in Hb.
cbn [YP09.c_off] in Hm. rewrite Z.add_0_r in Hm. unfold aview. rewrite Hm.
injection Hb as <-. cbn [option_map]. f_equal.
all: cbn [sv_denot]; rewrite ?Z.mul_0_r, ?Z.shiftr_0_r, ?unsigned_lit, ?Z_to_bv_unsigned;
     try (unfold bv_wrap; change (bv_modulus 8) with 256; reflexivity).
Qed.

(* the engine's `andi sp,sp,-0x20` mask, as a 64-bit literal, is the model's -32 on a 64-bit value *)
Lemma pbF_land_m32 : forall v, 0 <= v < 2 ^ 64 -> Z.land v (2 ^ 64 - 32) = Z.land v (-32).
Proof.
intros v Hv. replace (2 ^ 64 - 32) with (Z.land (Z.ones 64) (-32)) by (vm_compute; reflexivity).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.

Local Notation ctx := (hp_ctx (segs := rsegs)).

(* the entry state of the header tests, with the pod's header as a read-only region at a0 *)
Lemma pbE_entry_hdr : forall (x : ctx) (F : bvmap 5 word) (fc : bv 32) regs mem md (big : bool),
call_ok B x -> hx_null x = 0 ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md ->
getr regs 10 = w64 (hx_P x) ->
(if big then 16 else 8) <= hx_len x ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs (hgh_L x)) (pbE_ss_hdr big)
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_HDR) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx (pbE_SH big) (hk_env x regs (hgh_L x)) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x F fc regs mem md big Hc Hnull HC H10 Hbig.
pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (hk_pod B x Hc Hnull) as
  (HP0 & HP16 & Hlen & Hlmod & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & _).
pose proof (hk_pod_at_cut B pb_segs_low x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md
  errno_low Hc Hnull HC ltac:(cbn [length]; lia)) as (HG & HRA & _).
pose proof (hk_core_cregs B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md HC) as HCR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPhi : hx_P x + 16 <= 2 ^ 47)
by (destruct HAM as [HL | [HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *;
    destruct big; lia).
set (E := hk_env x regs (hgh_L x)).
assert (HE10 : ew E 10 = w64 (hx_P x))
by (subst E; rewrite (hk_env_reg x regs (hgh_L x) 10%nat (10%bv : bv 5) eq_refl); exact H10).
assert (HE27 : ew E 27 = w64 SHADOW_OFF)
by (subst E; rewrite (hk_env_reg x regs (hgh_L x) 27%nat (27%bv : bv 5) eq_refl);
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HCR))))))))).
assert (HU10 : bv_unsigned (ew E 10) = hx_P x)
by (rewrite HE10; apply unsigned_lit_small; lia).
assert (HB10 : base_val E (Some 10%nat) = hx_P x) by (cbn [base_val]; exact HU10).
assert (Hu32 : forall j, (j < 3)%nat -> ew E (47 + j) = w64 (Spa.u32_at (hx_bs x) (4 * Z.of_nat j)))
by (subst E; apply hgh_env_u32).
split.
- rewrite restrict_mkst_fx. unfold pbE_ss_hdr.
  change (hk_env x regs (hgh_L x)) with E.
  apply (entry_st_ok_full rsegs); change (hk_env x regs (hgh_L x)) with E.
  + apply regs_ok_Ereg.
  + destruct big; vm_compute; reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold pbE_pod_rg; destruct big;
    apply (hgh_region_ok E _ 10%nat (hx_P x)); [exact HU10 | lia | lia | | exact HU10 | lia | lia | ];
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 4 (SOff ?n 0))) =>
      let j := eval vm_compute in (Nat.sub n 47) in
      apply (chunk_ok_val rsegs E _ (hx_P x) off 4 (SOff n 0) (Spa.u32_at (hx_bs x) off));
      [ rewrite hk_sv_SOff0; change n with (47 + j)%nat; rewrite (Hu32 j ltac:(lia)); reflexivity
      | apply hgw_u32_range | lia
      | apply (hgw_pod_u32 (hx_rd x mem) (hx_P x) (hx_bs x) off HG ltac:(lia)
          ltac:(cbn in Hbig; unfold hx_len in *; lia)) ]
    end.
  + destruct big; repeat split.
  + split; [|split; [exact I | exact I]].
    unfold pbE_hdr_atoms. apply (hk_atoms_ok B x regs (hgh_L x) _ Hc HCR).
    cbn [atoms_ok].
    split; [apply hgh_afact_P; [exact H10 | lia | lia | exact HP16]|].
    split; [apply (hgh_afact_u32 x regs 47%nat 0%nat); [lia | reflexivity]|].
    split; [apply (hgh_afact_u32 x regs 48%nat 1%nat); [lia | reflexivity]|].
    split; [apply (hgh_afact_u32 x regs 49%nat 2%nat); [lia | reflexivity]|].
    exact I.
- unfold sh_ok, pbE_SH. apply Forall_cons; [|apply Forall_nil].
  apply (hk_shent_pod B x (w_H (hx_W x)) mem E 10%nat 0 0 (if big then 16 else 8) Hc Hnull HE27);
  [ rewrite Z.add_0_r; exact HE10 | exact HRA | lia | lia | destruct big; lia | destruct big; cbn in Hbig; lia ].
Qed.

(* ---------------------------------- the leaves of the header tests ---------------------------------- *)
(* every exit of this segment that returns: EPI with the answer (rc, [], (0, 0, NONE)) *)
Lemma pbE_epi_leaf : forall (x : ctx) (F : bvmap 5 word) (fc : bv 32) regs mem md regs2 md2 rc0,
call_ok B x -> EPI_ok B MT x ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md -> hp_fx F fc ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 -> getr regs2 20 = w64 rc0 ->
hx_ans x = (rc0, [], (0, 0, Headamp.REFUSE_NONE)) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_EPI regs2 mem md2) (PPOST B MT x).
Proof.
intros x F fc regs mem md regs2 md2 rc0 Hc HE HC HFX HAJ Hio HCR2 H20 Hans.
pose proof (hk_out B x Hc) as (Hcap & _).
apply (HE F fc). unfold EPI_at. rewrite Hans.
cbn [ans_cells ans_res_bytes ans_rc ans_n ans_keys ans_rf fst snd].
split; [|split; [exact HFX | rewrite H20; reflexivity]].
eapply (hk_core_frame B pb_segs_low x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md regs2 mem md2 0 0);
  [ exact errno_low | exact Hc | exact HC | cbn [length]; lia | reflexivity | lia | lia
  | intros a Ha Hn; reflexivity | exact HAJ | exact Hio | exact HCR2 ].
Qed.

(* the one exit that goes on: the find loop at r = 16 *)
Lemma pbE_find_leaf : forall (x : ctx) (F : bvmap 5 word) (fc : bv 32) regs mem md regs2 md2,
call_ok B x -> (forall r n, FIND_ok B MT x r n) -> hx_null x = 0 ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md -> hp_fx F fc ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 ->
Spa.is_object_type (hx_bs x) Model.POD_OBJECT_PROPS = true -> 16 <= hx_SZ x ->
getr regs2 10 = w64 (hx_P x + 8) -> getr regs2 11 = w64 (hx_P x + 16) ->
getr regs2 12 = w64 (hx_SZ x - 16) -> getr regs2 13 = w64 (hx_P x + hx_SZ x - 8) ->
getr regs2 14 = w64 Model.POD_PROP_PARAMS -> getr regs2 20 = w64 0 ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_FIND regs2 mem md2) (PPOST B MT x).
Proof.
intros x F fc regs mem md regs2 md2 Hc HF Hnull HC HFX HAJ Hio HCR2 Hobj HSZ16 Q10 Q11 Q12 Q13 Q14 Q20.
pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlmod & HSZ & HP63 & _).
apply (HF 16 (S (Z.to_nat (8 + hx_SZ x - 16))) F fc).
unfold FIND_at.
split; [|split; [exact HFX|]].
- eapply (hk_core_frame B pb_segs_low x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md regs2 mem md2 0 0);
    [ exact errno_low | exact Hc | exact HC | cbn [length]; lia | reflexivity | lia | lia
    | intros a Ha Hn; reflexivity | exact HAJ | exact Hio | exact HCR2 ].
- split.
  + unfold hp_m_find.
    split; [exact Hnull|]. split; [exact Hobj|]. split; [lia|].
    split; [unfold hx_len in *; lia|]. split; [reflexivity|]. split; [lia|].
    apply (hgh_res_find x (S (Z.to_nat (8 + hx_SZ x - 16))) Hobj); [lia|].
    unfold hx_len in *. lia.
  + split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
    split; [exact Q14 | exact Q20].
Qed.

(* the two ways this segment ends, as one step each *)
Ltac pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE rcv Hans :=
let Hm := fresh "Hm" in
pbE_mem_eq mem Hm;
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite Hm in HJ end;
lazymatch goal with HS2 : st_ok _ _ _ (restrict _ ?msn) |- _ =>
  let Hshape := fresh "Hshape" in let R20 := fresh "R20" in let HKR := fresh "HKR" in
  pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ msn HS2 eq_refl) as Hshape;
  rreg HS2 (20%bv : bv 5) R20;
  pose proof (regs_kept_of_st_ok rsegs _ _ (restrict (w_H (hx_W x)) msn) regs _
    [2; 3; 4; 8; 9; 18; 19; 26; 27]%bv HS2 ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR;
  cbn [ms_regs restrict] in HKR;
  rewrite Hshape;
  lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md2) ?Q =>
    change (SRr s W (cfg_at (fx := mkFP F fc) rsegs PC_EPI rg mm md2) Q) end;
  rewrite Hm;
  eapply (pbE_epi_leaf x F fc regs mem md _ _ rcv Hc HE HC HFX);
    [ eassumption | hgh_io
    | eapply hk_cregs_same; solve [exact HCR | apply HKR; cbv [In]; tauto]
    | rewrite R20; apply bv_eq; vm_compute; reflexivity
    | exact Hans ]
end.

(* ---------------------------------- the header tests, non-NULL ---------------------------------- *)
Lemma pbE_hdr_nonnull : forall (x : ctx), call_ok B x -> EPI_ok B MT x ->
(forall r n, FIND_ok B MT x r n) -> hx_null x = 0 ->
forall F fc regs mem md, pbE_hdr B x F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_HDR regs mem md) (PPOST B MT x).
Proof.
intros x Hc HE HF Hnull F fc regs mem md (HC & HFX & Ha0).
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
unfold pbE_a0 in Ha0. rewrite Hnull in Ha0. cbn [Z.eqb] in Ha0.
pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlmod & HSZ & HP63 & _).
pose proof (hk_core_journal B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md HC) as (HAJ & HST & HPAT).
pose proof (hk_core_cregs B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md HC) as HCR.
pose proof (hk_core_io B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md HC) as Hio0.
pose proof (hgw_u32_range (hx_bs x) 0) as R0.
pose proof (hgw_u32_range (hx_bs x) 4) as R4.
pose proof (hgw_u32_range (hx_bs x) 8) as R8.
assert (HAE : env_agree 32 (hk_env x regs (hgh_L x)) (hk_env x regs (hgh_L x))) by apply env_agree_refl.
assert (E47 : ew (hk_env x regs (hgh_L x)) 47 = w64 (Spa.u32_at (hx_bs x) 0))
by (change 47%nat with (47 + 0)%nat; rewrite (hgh_env_u32 x regs 0%nat ltac:(lia)); reflexivity).
assert (E48 : ew (hk_env x regs (hgh_L x)) 48 = w64 (Spa.u32_at (hx_bs x) 4))
by (change 48%nat with (47 + 1)%nat; rewrite (hgh_env_u32 x regs 1%nat ltac:(lia)); reflexivity).
assert (E49 : ew (hk_env x regs (hgh_L x)) 49 = w64 (Spa.u32_at (hx_bs x) 8))
by (change 49%nat with (47 + 2)%nat; rewrite (hgh_env_u32 x regs 2%nat ltac:(lia)); reflexivity).
assert (E10 : ew (hk_env x regs (hgh_L x)) 10 = w64 (hx_P x))
by (rewrite (hk_env_reg x regs (hgh_L x) 10%nat (10%bv : bv 5) eq_refl); exact Ha0).
unfold hx_SZ in HSZ.
destruct (Z_lt_le_dec (hx_len x) 16) as [Hsmall | Hbig].
- (* the pod is eight bytes: the size word is 0, so the run returns -1 at the `bltu size, 8` *)
  assert (HS0 : Spa.u32_at (hx_bs x) 0 = 0) by (unfold hx_len in *; lia).
  assert (Hans : hx_ans x = (-1, [], (0, 0, Headamp.REFUSE_NONE)))
  by (rewrite (hgh_ans_res x Hnull); apply hgh_res_notprops; apply hgh_obj_small; lia).
  destruct (pbE_entry_hdr x F fc regs mem md false Hc Hnull HC Ha0 ltac:(cbn; lia)) as [HS SHOK].
  unfold cfg_at. change (w64 PC_HDR) with (Z_to_bv 64 PC_HDR).
  pbE_run; [pbE_awr_ro | ].
  pbE_branch Hc1.
  { (* size >> 20 <> 0 is impossible *)
    exfalso.
    lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
      assert (E47' : ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0))
      by (repeat rewrite ew_ewset_other by lia; exact E47) end.
    rewrite branch_ne_U in Hc1.
    lazymatch goal with E47' : ew ?E2 47 = _ |- _ =>
      rewrite (hgh_U_srliw20 E2 47 (Spa.u32_at (hx_bs x) 0) E47' ltac:(lia)) in Hc1 end.
    rewrite U_lit in Hc1 by lia.
    apply negb_true_iff, Z.eqb_neq in Hc1. apply Hc1. rewrite HS0. reflexivity. }
  pbE_run_to PC_EPI; [pbE_awr_ro | ].
  pbE_branch Hc2.
  2:{ (* size >= 8 is impossible: the pod is eight bytes *)
      exfalso.
      lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
        assert (E47' : ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0))
        by (repeat rewrite ew_ewset_other by lia; exact E47) end.
      rewrite branch_ltu_U in Hc2.
      lazymatch goal with E47' : ew ?E2 47 = _ |- _ =>
        rewrite (hgh_U_sx32 E2 47 (Spa.u32_at (hx_bs x) 0) E47' ltac:(lia)) in Hc2 end.
      rewrite U_lit in Hc2 by lia.
      apply Z.ltb_ge in Hc2. lia. }
  (* the `bltu size, 8` is taken and the run reaches the epilogue *)
  pbE_run_to PC_EPI; [pbE_awr_ro | ].
  pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE (-1) Hans.
- (* the pod has at least sixteen bytes: the four header tests, then the find setup *)
  assert (Hlen16 : 16 <= hx_len x) by lia.
  destruct (pbE_entry_hdr x F fc regs mem md true Hc Hnull HC Ha0 ltac:(cbn; lia)) as [HS SHOK].
  unfold cfg_at. change (w64 PC_HDR) with (Z_to_bv 64 PC_HDR).
  (* 0x84ab4 .. 0x84ad8, stop at 0x84adc `bnez (size >> 20)` *)
  pbE_run; [pbE_awr_ro | ].
  pbE_branch Hc1.
  lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
    assert (E47a : ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0))
    by (repeat rewrite ew_ewset_other by lia; exact E47) end.
  all: rewrite branch_ne_U in Hc1.
  all: lazymatch goal with E47a : ew ?E2 47 = _ |- _ =>
         rewrite (hgh_U_srliw20 E2 47 (Spa.u32_at (hx_bs x) 0) E47a ltac:(lia)) in Hc1 end.
  all: rewrite U_lit in Hc1 by lia.
  { (* the size word is at least 2^20: not a Props object *)
    apply negb_true_iff, Z.eqb_neq in Hc1.
    assert (Hbigsz : 1048576 <= Spa.u32_at (hx_bs x) 0)
    by (destruct (Z_lt_le_dec (Spa.u32_at (hx_bs x) 0) 1048576) as [Hl|Hl];
        [exfalso; apply Hc1; apply Z.div_small; change (2 ^ 20) with 1048576; lia | lia]).
    assert (Hans : hx_ans x = (-1, [], (0, 0, Headamp.REFUSE_NONE)))
    by (rewrite (hgh_ans_res x Hnull); apply hgh_res_notprops; apply hgh_obj_big; lia).
    pbE_run_to PC_EPI; [pbE_awr_ro | ].
    pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE (-1) Hans. }
  apply negb_false_iff, Z.eqb_eq in Hc1.
  assert (HS20 : Spa.u32_at (hx_bs x) 0 < 1048576).
  { destruct (Z_lt_le_dec (Spa.u32_at (hx_bs x) 0) 1048576) as [Hl|Hl]; [exact Hl|].
    exfalso. pose proof (Z.div_le_mono 1048576 (Spa.u32_at (hx_bs x) 0) (2 ^ 20) ltac:(lia)
      ltac:(change (2 ^ 20) with 1048576; lia)) as Hd.
    rewrite Z.div_same in Hd by (change (2 ^ 20) with 1048576; lia). lia. }
  (* 0x84ae0 .. 0x84af4, stop at 0x84af8 `bltu size, 8` *)
  pbE_run; [pbE_awr_ro | ].
  pbE_branch Hc2.
  lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
    assert (E47b : ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0))
    by (repeat rewrite ew_ewset_other by lia; exact E47) end.
  all: rewrite branch_ltu_U in Hc2.
  all: lazymatch goal with E47b : ew ?E2 47 = _ |- _ =>
         rewrite (hgh_U_sx32 E2 47 (Spa.u32_at (hx_bs x) 0) E47b ltac:(lia)) in Hc2 end.
  all: rewrite U_lit in Hc2 by lia.
  { (* the size word is below 8: not a Props object *)
    apply Z.ltb_lt in Hc2.
    assert (Hans : hx_ans x = (-1, [], (0, 0, Headamp.REFUSE_NONE)))
    by (rewrite (hgh_ans_res x Hnull); apply hgh_res_notprops; apply hgh_obj_small; lia).
    pbE_run_to PC_EPI; [pbE_awr_ro | ].
    pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE (-1) Hans. }
  apply Z.ltb_ge in Hc2.
  (* 0x84afc .. 0x84b00, stop at 0x84b04 `bne type, 15` *)
  pbE_run; [pbE_awr_ro | ].
  pbE_branch Hc3.
  lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
    assert (E48a : ew E2 48 = w64 (Spa.u32_at (hx_bs x) 4))
    by (repeat rewrite ew_ewset_other by lia; exact E48) end.
  all: rewrite branch_ne_U in Hc3.
  all: lazymatch goal with E48a : ew ?E2 48 = _ |- _ =>
         rewrite (hgh_U_sx32_eqb E2 48 (Spa.u32_at (hx_bs x) 4) 15 E48a ltac:(lia) ltac:(lia)) in Hc3 end.
  { (* the type word is not Object *)
    apply negb_true_iff, Z.eqb_neq in Hc3.
    assert (Hans : hx_ans x = (-1, [], (0, 0, Headamp.REFUSE_NONE)))
    by (rewrite (hgh_ans_res x Hnull); apply hgh_res_notprops; apply hgh_obj_type; lia).
    pbE_run_to PC_EPI; [pbE_awr_ro | ].
    pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE (-1) Hans. }
  apply negb_false_iff, Z.eqb_eq in Hc3.
  (* 0x84b08 .. 0x84b24, stop at 0x84b28 `bne object type, 0x40002` *)
  pbE_run; [pbE_awr_ro | ].
  pbE_branch Hc4.
  lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
    assert (E49a : ew E2 49 = w64 (Spa.u32_at (hx_bs x) 8))
    by (repeat rewrite ew_ewset_other by lia; exact E49) end.
  all: rewrite branch_ne_U in Hc4.
  all: lazymatch goal with E49a : ew ?E2 49 = _ |- _ =>
         rewrite (hgh_U_sx32_eqb E2 49 (Spa.u32_at (hx_bs x) 8) 262146 E49a ltac:(lia) ltac:(lia)) in Hc4 end.
  { (* the object type is not Props *)
    apply negb_true_iff, Z.eqb_neq in Hc4.
    assert (Hans : hx_ans x = (-1, [], (0, 0, Headamp.REFUSE_NONE)))
    by (rewrite (hgh_ans_res x Hnull); apply hgh_res_notprops; apply hgh_obj_props; lia).
    pbE_run_to PC_EPI; [pbE_awr_ro | ].
    pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE (-1) Hans. }
  apply negb_false_iff, Z.eqb_eq in Hc4.
  assert (Hobj : Spa.is_object_type (hx_bs x) Model.POD_OBJECT_PROPS = true)
  by (apply hgh_obj_true; lia).
  (* 0x84b2c, stop at 0x84b30 `bgeu size, 16` *)
  pbE_run; [pbE_awr_ro | ].
  pbE_branch Hc5.
  lazymatch goal with HS2 : st_ok _ ?E2 _ _ |- _ =>
    assert (E47c : ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0))
    by (repeat rewrite ew_ewset_other by lia; exact E47) end.
  all: rewrite branch_geu_U in Hc5.
  all: lazymatch goal with E47c : ew ?E2 47 = _ |- _ =>
         rewrite (hgh_U_sx32 E2 47 (Spa.u32_at (hx_bs x) 0) E47c ltac:(lia)) in Hc5 end.
  all: rewrite U_lit in Hc5 by lia.
  2:{ (* the size word is below 16: no params property, rc 0 *)
      apply negb_false_iff, Z.ltb_lt in Hc5.
      assert (Hans : hx_ans x = (0, [], (0, 0, Headamp.REFUSE_NONE))).
      { rewrite (hgh_ans_res x Hnull). apply (hgh_res_noparams x Hobj).
        apply hgh_find_none; [unfold hx_len in *; lia | lia]. }
      pbE_run_to PC_EPI; [pbE_awr_ro | ].
      pbE_fin_epi x F fc regs mem md Hc HE HC HFX HCR HAE 0 Hans. }
  (* the size word is at least 16: the find setup, then the find loop at r = 16 *)
  apply negb_true_iff, Z.ltb_ge in Hc5.
  pbE_run_to PC_FIND; [pbE_awr_ro | ].
  pbE_mem_eq mem Hm.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite Hm in HJ end.
  lazymatch goal with HS2 : st_ok _ ?E2 _ (restrict _ ?msn) |- _ =>
    assert (E47d : ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0))
      by (repeat rewrite ew_ewset_other by lia; exact E47);
    assert (E10d : ew E2 10 = w64 (hx_P x))
      by (repeat rewrite ew_ewset_other by lia; exact E10);
    pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ msn HS2 eq_refl) as Hshape;
    pbE_reg HS2 (10%bv : bv 5) Q10; pbE_reg HS2 (11%bv : bv 5) Q11; pbE_reg HS2 (12%bv : bv 5) Q12;
    pbE_reg HS2 (13%bv : bv 5) Q13; pbE_reg HS2 (14%bv : bv 5) Q14; pbE_reg HS2 (20%bv : bv 5) Q20;
    pose proof (regs_kept_of_st_ok rsegs _ _ (restrict (w_H (hx_W x)) msn) regs _
      [2; 3; 4; 8; 9; 18; 19; 26; 27]%bv HS2 ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR
  end.
  cbn [ms_regs restrict] in HKR.
  rewrite Hshape.
  lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md2) ?Q =>
    change (SRr s W (cfg_at (fx := mkFP F fc) rsegs PC_FIND rg mm md2) Q) end.
  rewrite Hm.
  assert (USZ : forall E2, ew E2 47 = w64 (Spa.u32_at (hx_bs x) 0) ->
    U E2 (SExt true 32 (SOff 47 0)) = Spa.u32_at (hx_bs x) 0)
  by (intros E2 HE2; apply (hgh_U_sx32 E2 47 _ HE2); lia).
  eapply (pbE_find_leaf x F fc regs mem md _ _ Hc HF Hnull HC HFX);
    [ eassumption | hgh_io
    | eapply hk_cregs_same; solve [exact HCR | apply HKR; cbv [In]; tauto]
    | exact Hobj | unfold hx_SZ; lia
    | rewrite Q10, denot_lit_U, (U_atom_off _ 10 (hx_P x) 8 E10d ltac:(lia) ltac:(lia)); reflexivity
    | rewrite Q11, denot_lit_U, (U_atom_off _ 10 (hx_P x) 16 E10d ltac:(lia) ltac:(lia)); reflexivity
    | rewrite Q12, denot_lit_U, (hgh_U_add_lit _ _ _ (-16) (USZ _ E47d) ltac:(lia) ltac:(lia));
      unfold hx_SZ; reflexivity
    | rewrite Q13, denot_lit_U,
        (hgh_U_add2 _ _ _ _ _ (hgh_U_add_lit _ _ _ (-16) (USZ _ E47d) ltac:(lia) ltac:(lia))
           (U_atom_off _ 10 (hx_P x) 8 E10d ltac:(lia) ltac:(lia)) ltac:(lia));
      unfold hx_SZ, w64; f_equal; lia
    | rewrite Q14; apply bv_eq; vm_compute; reflexivity
    | rewrite Q20; apply bv_eq; vm_compute; reflexivity ].
Qed.

(* ---------------------------------- the three `sw zero` at res ---------------------------------- *)
Lemma pbE_entry_res : forall (x : ctx) (F : bvmap 5 word) (fc : bv 32) regs mem md,
call_ok B x -> hx_R x <> 0 -> pbE_core0 B x regs mem md ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs []) pbE_ss_res
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_RES) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx pbE_SH_res (hk_env x regs []) (mrestrict (w_H (hx_W x)) mem) /\
range_addressable (aview rsegs (w_H (hx_W x)) mem) SHADOW_OFF (hx_R x) 12.
Proof.
intros x F fc regs mem md Hc HR0 HC0.
pose proof (pbE_cregs_of_core0 B x regs mem md HC0) as HCR.
pose proof (hgh_res_bounds B pb_segs_low x Hc HR0) as (RB1 & RB2 & RB3).
pose proof (hk_res B pb_segs_low x Hc HR0) as (_ & HRA0 & Hside & _).
pose proof HC0 as (HJ & Hio & HK & HSV & HEv & HPR & _).
pose proof HCR as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
set (E := hk_env x regs (@nil word)).
assert (HE9 : ew E 9 = w64 (hx_R x))
by (subst E; rewrite (hk_env_reg x regs (@nil word) 9%nat (9%bv : bv 5) eq_refl); exact C9).
assert (HE27 : ew E 27 = w64 SHADOW_OFF)
by (subst E; rewrite (hk_env_reg x regs (@nil word) 27%nat (27%bv : bv 5) eq_refl); exact C27).
assert (HU9 : bv_unsigned (ew E 9) = hx_R x)
by (rewrite HE9; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616;
    change (2 ^ 47) with 140737488355328 in RB2; lia).
(* the shadow of res is readable at this cut: it is readable at the call and nothing changed it *)
assert (HRA : range_addressable (aview rsegs (w_H (hx_W x)) mem) SHADOW_OFF (hx_R x) 12).
{ intros a Ha. destruct (HRA0 a Ha) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hsv.
  assert (Hlow : 0 <= shadow_addr a < alloc_ceiling)
  by (apply hgh_sh_low; change (2 ^ 47) with 140737488355328 in RB2 |- *; lia).
  replace (shadow_of_addr SHADOW_OFF a) with (shadow_addr a) by reflexivity.
  apply (HK (shadow_addr a)).
  - pose proof ASAN_CEIL_range as [[A1 A2] _]. unfold ASAN_CEIL in A2.
    change (2 ^ 64) with 18446744073709551616. lia.
  - intros Hw. pose proof (hk_window_band B x (shadow_addr a) Hc Hw) as (Hw1 & _). lia.
  - replace a with (hx_R x + (a - hx_R x)) by lia.
    apply (hgh_sh_res_not_hole B pb_segs_low x Hc HR0). lia. }
split; [|split; [|exact HRA]].
- rewrite restrict_mkst_fx. unfold pbE_ss_res.
  change (hk_env x regs (@nil word)) with E.
  apply (entry_st_ok_full rsegs); change (hk_env x regs (@nil word)) with E.
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold pbE_res_rg.
    apply (hgh_region_w E _ 9%nat (hx_R x) 0 12 HU9 ltac:(lia)
      ltac:(change (2 ^ 64) with 18446744073709551616;
            change (2 ^ 47) with 140737488355328 in RB2; lia)).
    intros o Ho. apply (apresent_writable rsegs). apply HPR; [exact HR0 | lia].
  + repeat split.
  + split; [|split; [exact I | exact I]].
    unfold pbE_res_atoms. apply (hk_atoms_ok B x regs (@nil word) _ Hc HCR). fold E.
    cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite HU9. change (2 ^ 2) with 4.
    split; [repeat split; lia | exact I].
- unfold sh_ok, pbE_SH_res. apply Forall_cons; [|apply Forall_nil].
  apply (hk_shent_res B pb_segs_low x (w_H (hx_W x)) mem E 9%nat 0 12 Hc HR0 HE27 HE9 HRA);
    [lia | lia].
Qed.

(* ---------------------------------- the header tests, either argument ---------------------------------- *)
Lemma pbE_hdr_ok : forall (x : ctx), call_ok B x -> EPI_ok B MT x ->
(forall r n, FIND_ok B MT x r n) ->
forall F fc regs mem md, pbE_hdr B x F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_HDR regs mem md) (PPOST B MT x).
Proof.
intros x Hc HE HF F fc regs mem md Hp.
pose proof (hk_call_regs B x Hc) as (Hn01 & _).
destruct (Z.eq_dec (hx_null x) 0) as [Hz|Hz].
- apply (pbE_hdr_nonnull x Hc HE HF Hz F fc regs mem md Hp).
- apply (pbE_hdr_null B MT x HE ltac:(lia) F fc regs mem md Hp).
Qed.

Lemma pbE_entry_res0 : forall (x : ctx) (F : bvmap 5 word) (fc : bv 32) regs mem,
getr regs 9 = w64 0 ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs (@nil word)) pbE_ss_res0
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_RES) mem (seg_rom rsegs))).
Proof.
intros x F fc regs mem H9.
rewrite restrict_mkst_fx. unfold pbE_ss_res0.
apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | |].
  + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
  + rewrite H9. reflexivity.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Lemma pbE_res_ok : forall (x : ctx), call_ok B x -> EPI_ok B MT x ->
(forall r n, FIND_ok B MT x r n) ->
forall F fc regs mem md, pbE_pre B x F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_RES regs mem md) (PPOST B MT x).
Proof.
intros x Hc HE HF F fc regs mem md (HC0 & HFX & Ha0).
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
pose proof (pbE_cregs_of_core0 B x regs mem md HC0) as HCR.
pose proof HC0 as (HJ0 & Hio0 & HK0 & HSV0 & HEv0 & HPR0 & _).
pose proof HJ0 as (HAJ & HST & HPAT).
pose proof HCR as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
assert (HAE : env_agree 32 (hk_env x regs (@nil word)) (hk_env x regs (@nil word)))
by apply env_agree_refl.
unfold cfg_at. change (w64 PC_RES) with (Z_to_bv 64 PC_RES).
destruct (Z.eq_dec (hx_R x) 0) as [HR0|HR0].
- (* res is NULL: the `beqz s1` is taken and nothing is written *)
  assert (H9 : getr regs 9 = w64 0) by (rewrite C9, HR0; reflexivity).
  pose proof (pbE_entry_res0 x F fc regs mem H9) as HS.
  aj_run_toH pb_tbl_ok HS HAJ PC_HDR.
  { apply awr_okH_nil. }
  pbE_mem_eq mem Hm.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite Hm in HJ end.
  lazymatch goal with HS2 : st_ok _ _ _ (restrict _ ?msn) |- _ =>
    pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ msn HS2 eq_refl) as Hshape;
    pbE_reg HS2 (9%bv : bv 5) Q9;
    pose proof (regs_kept_of_st_ok rsegs _ _ (restrict (w_H (hx_W x)) msn) regs _
      [2; 3; 4; 8; 10; 18; 19; 26; 27]%bv HS2 ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR
  end.
  cbn [ms_regs restrict] in HKR.
  rewrite Hshape.
  lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md2) ?Q =>
    change (SRr s W (cfg_at (fx := mkFP F fc) rsegs PC_HDR rg mm md2) Q) end.
  rewrite Hm.
  apply (pbE_hdr_ok x Hc HE HF).
  split; [|split; [exact HFX|]].
  + eapply (hk_core_intro B pb_segs_low x _ mem _ errno_low Hc);
      [ eassumption | exact HST | exact HPAT | hgh_io
      | intros a Ha Hw Hh _; exact (HK0 a Ha Hw Hh) | exact HSV0
      | intros Hne; exfalso; exact (Hne HR0)
      | eapply hk_cregs_same;
        [ exact HCR
        | apply HKR; cbv [In]; tauto | apply HKR; cbv [In]; tauto | apply HKR; cbv [In]; tauto
        | apply HKR; cbv [In]; tauto
        | rewrite Q9, H9; reflexivity
        | apply HKR; cbv [In]; tauto | apply HKR; cbv [In]; tauto | apply HKR; cbv [In]; tauto
        | apply HKR; cbv [In]; tauto ] ].
  + unfold pbE_a0. rewrite (HKR (10%bv : bv 5) ltac:(cbv [In]; tauto)). exact Ha0.
- (* res is not NULL: the three instrumented `sw zero` *)
  destruct (pbE_entry_res x F fc regs mem md Hc HR0 HC0) as (HS & SHOK & HRA).
  aj_run_to_tokH pb_tbl_ok HS HAJ SHOK hk_Bspan PC_HDR.
  { lazymatch goal with |- awr_okH ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?U =>
      let rs' := eval vm_compute in rs in change (awr_okH E rs' stk sp0 fp b0 bc ly own U) end.
    eapply (hk_awr_res B pb_segs_low x);
      [ exact Hc | exact HR0 | reflexivity
      | rewrite (hk_env_reg x regs (@nil word) 9%nat (9%bv : bv 5) eq_refl), C9;
        apply unsigned_lit_small;
        pose proof (hgh_res_bounds B pb_segs_low x Hc HR0) as (RB1 & RB2 & RB3);
        change (2 ^ 64) with 18446744073709551616;
        change (2 ^ 47) with 140737488355328 in RB2; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; lia
      | apply awr_okH_nil ]. }
  (* the three zero words are in res; nothing else changed *)
  lazymatch goal with HS2 : st_ok _ ?E2 _ (restrict _ ?msn) |- _ =>
    assert (HU9 : bv_unsigned (ew E2 9) = hx_R x)
    by (repeat rewrite ew_ewset_other by lia;
        rewrite (hk_env_reg x regs (@nil word) 9%nat (9%bv : bv 5) eq_refl), C9;
        apply unsigned_lit_small;
        pose proof (hgh_res_bounds B pb_segs_low x Hc HR0) as (RB1 & RB2 & RB3);
        change (2 ^ 64) with 18446744073709551616;
        change (2 ^ 47) with 140737488355328 in RB2; lia);
    pose proof (st_ok_mem_ok rsegs _ _ _ HS2) as (_ & HRs & _) end.
  cbn [ss_mem ms_mem restrict] in HRs.
  apply Forall_cons_iff in HRs as [HR1 _].
  unfold region_ok in HR1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR1.
  destruct HR1 as (_ & _ & _ & HCs).
  apply Forall_cons_iff in HCs as [K8 HCs].
  apply Forall_cons_iff in HCs as [K4 HCs].
  apply Forall_cons_iff in HCs as [K0 _].
  rewrite HU9 in K0, K4, K8.
  lazymatch goal with HS2 : st_ok _ ?E2 _ (restrict _ ?msn) |- _ =>
    pose proof (val_of_chunk_ok rsegs E2 _ (hx_R x) 0 4 (SLit 0) 0 K0 eq_refl ltac:(zside) ltac:(zside)) as V0;
    pose proof (val_of_chunk_ok rsegs E2 _ (hx_R x) 4 4 (SLit 0) 0 K4 eq_refl ltac:(zside) ltac:(zside)) as V4;
    pose proof (val_of_chunk_ok rsegs E2 _ (hx_R x) 8 4 (SLit 0) 0 K8 eq_refl ltac:(zside) ltac:(zside)) as V8
  end.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V4, V8.
  rewrite Z.add_0_r in V0.
  (* the run's only write window is res *)
  assert (HWR : forall a (r : YP09.region), In r (ss_mem pbE_ss_res) ->
    base_val (hk_env x regs (@nil word)) (YP09.r_base r) + YP09.r_wlo r <= a <
    base_val (hk_env x regs (@nil word)) (YP09.r_base r) + YP09.r_whi r ->
    hx_R x <= a < hx_R x + 12).
  { intros a r Hin Hb. cbv [ss_mem pbE_ss_res pbE_res_rg] in Hin. cbn [In] in Hin.
    destruct Hin as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
    rewrite (hk_env_reg x regs (@nil word) 9%nat (9%bv : bv 5) eq_refl), C9 in Hb.
    rewrite unsigned_lit_small in Hb by
      (pose proof (hgh_res_bounds B pb_segs_low x Hc HR0) as (RB1 & RB2 & RB3);
       change (2 ^ 64) with 18446744073709551616;
       change (2 ^ 47) with 140737488355328 in RB2; lia).
    lia. }
  lazymatch goal with HF2 : frame_of _ _ _ (ms_mem ?msn) |- _ =>
    assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_R x <= a < hx_R x + 12) ->
      hx_view x (ms_mem msn) a = hx_view x mem a)
    by (intros aa Haa0 Haa; apply (hgh_view_kept x mem (ms_mem msn) aa); apply HF2;
        intros (rr & Hinn & Hbb); rewrite unsigned_lit_small in Hbb by exact Haa0;
        exact (Haa (HWR aa rr Hinn Hbb)))
  end.
  pose proof (hk_res B pb_segs_low x Hc HR0) as (_ & _ & Hside & _).
  lazymatch goal with HS2 : st_ok _ _ _ (restrict _ ?msn) |- _ =>
    pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ msn HS2 eq_refl) as Hshape;
    pose proof (regs_kept_of_st_ok rsegs _ _ (restrict (w_H (hx_W x)) msn) regs _
      [2; 3; 4; 8; 9; 10; 18; 19; 26; 27]%bv HS2 ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKR
  end.
  cbn [ms_regs restrict] in HKR.
  rewrite Hshape.
  lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md2) ?Q =>
    change (SRr s W (cfg_at (fx := mkFP F fc) rsegs PC_HDR rg mm md2) Q) end.
  apply (pbE_hdr_ok x Hc HE HF).
  split; [|split; [exact HFX|]].
  + eapply (hk_core_intro B pb_segs_low x _ _ _ errno_low Hc);
      [ eassumption | exact HST
      | (* hpat *) apply (hk_hpat_kept x mem _ PAT_KEY); [|exact HPAT];
        intros i Hi; change (Z.of_nat (length PAT_KEY)) with 8 in Hi;
        assert (Hin : hp_hole x (hx_shf x + i)) by (unfold hp_hole; lia);
        pose proof (hk_hole_band B x (hx_shf x + i) Hc Hin) as (HB1 & HB2);
        apply HKEEP;
        [ pose proof ASAN_CEIL_range as [[A1 A2] _]; unfold ASAN_CEIL in A2;
          unfold SHADOW_OFF, kHighShadowEnd in HB1;
          change (2 ^ 64) with 18446744073709551616; change (2 ^ 43) with 8796093022208 in HB1; lia
        | intros Hbad; exact (hgh_res_not_hole B pb_segs_low x Hc HR0 (hx_shf x + i) Hbad Hin) ]
      | hgh_io
      | (* kept *) intros a Ha Hw Hh Hr; rewrite (HKEEP a Ha ltac:(tauto)); exact (HK0 a Ha Hw Hh)
      | (* saved *) apply (hk_saved_kept x mem); [|exact HSV0];
        intros a Ha;
        assert (Hwin : hx_sp x - T_parse_STK <= a < hx_sp x)
          by (unfold T_parse_STK, T_PARSE_FRAME, ESTACK; lia);
        pose proof (hk_window_band B x a Hc Hwin) as (HW1 & HW2);
        apply HKEEP;
        [ pose proof ASAN_CEIL_range as [[A1 A2] _]; unfold ASAN_CEIL in A1;
          change (2 ^ 64) with 18446744073709551616;
          change (2 ^ 47) with 140737488355328 in HW2; lia
        | unfold T_parse_STK, T_PARSE_FRAME, ESTACK in Hside; lia ]
      | (* res *) intros _; apply hgh_res_garr8; apply (hgh_res_zero _ (hx_R x) V0 V4 V8)
      | eapply hk_cregs_same; solve [exact HCR | apply HKR; cbv [In]; tauto] ].
  + unfold pbE_a0. rewrite (HKR (10%bv : bv 5) ltac:(cbv [In]; tauto)). exact Ha0.
Qed.

(* ---------------------------------- the prologue ---------------------------------- *)
Hypothesis HBgot : as_got_shadow B = PB_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = PB_SH_CELL.

(* What the walk holds at 0x84a64: the cut-state form with the hole open at PAT_KEY, the saves in the frame, every
   byte outside the parse's stack window and the hole as at the call, and the registers the prologue set. *)
Definition pbE_mid (x : pctx) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem md (hx_k x) (hx_fr x) PAT_KEY /\
same_io (hx_mdc x) md /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
 hx_view x mem a = hx_view x (hx_memc x) a) /\
hp_saved_ok x mem /\
(forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) mem a) /\
hk_cregs x regs /\
getr regs 10 = w64 (if hx_null x =? 0 then hx_P x else 0).

(* ---------------------------------- chunk A, the fsd, chunk B ---------------------------------- *)
Lemma pbF_entry : forall x : pctx, call_ok B x ->
(forall regs mem md, pbE_mid x regs mem md ->
 SRr rsegs (hx_W x) (cfg_at rsegs PC_RES regs mem md) (PPOST B MT x)) ->
SRr rsegs (hx_W x) (cfg_at rsegs B_PARSE_RESULT (hx_regs x) (hx_memc x) (hx_mdc x)) (PPOST B MT x).
Proof.
intros x Hc HK.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
pose proof (hk_call_pre B x Hc) as HPRE.
pose proof (hk_call_journal B x Hc) as HJ0.
pose proof (hk_call_regs B x Hc) as (Hnull & H10 & H11 & H12 & H13 & Hra & Hra4 & Hgp & Htp).
pose proof (hk_stack B x Hc) as HST.
pose proof (hk_frame_win B x Hc) as HFW.
pose proof (@ASAN_CEIL_range rc) as [[AC1 AC2] _]. unfold ASAN_CEIL in AC1, AC2.
destruct HST as (ST1 & ST2 & ST3 & ST4 & ST5 & ST6 & ST7 & ST8 & ST9 & ST10 & ST11 & ST12 & ST13).
destruct HFW as (FW1 & FW2 & FW3 & FW4 & FW5).
assert (Hpres0 : forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) (hx_memc x) a).
{ pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *.
(* ---------------- chunk A: the prologue's thirteen `sd` ---------------- *)
set (E0 := Ereg (hx_regs x) (@nil word)).
assert (U2 : bv_unsigned (ew E0 2) = hx_sp x)
  by (subst E0; rewrite (ew_Ereg_nat (hx_regs x) (@nil word) 2 2%bv eq_refl); reflexivity).
assert (HS0 : st_ok rsegs E0 ss_pbA
  (restrict (w_H (hx_W x)) (@mkst fx (hx_regs x) (Z_to_bv 64 B_PARSE_RESULT) (hx_memc x) (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_pbA. subst E0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pbA_stk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpres0. lia.
  - cbn; auto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U2. change (2 ^ 4) with 16. repeat split; lia. }
unfold cfg_at. change (w64 B_PARSE_RESULT) with (Z_to_bv 64 B_PARSE_RESULT).
aj_run_to pb_tbl_ok HS0 HJ0 PF_FSD.
{ eapply (awr_ok_cons_stack_off E0 pbA_stk [] (hx_STK x) (hx_sp0 x) (hx_FP x) _ _ (hx_lyc x) (hx_own x)
    2%nat (hx_sp x - hx_sp0 x)); [reflexivity | rewrite U2; lia | unfold pbA_stk; cbn [YP09.r_wlo]; lia
   | unfold pbA_stk; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* the thirteen saved words, read back out of the stack region's chunks *)
lazymatch goal with HS0 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
assert (Hpres1 : forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) (ms_mem ms1) a).
{ pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
assert (HSV0 : Forall (fun c => val_mem rsegs (mrestrict (w_H (hx_W x)) (ms_mem ms1)) (hx_sp x + fst c) 8
   (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 (snd c))))) HP_SAVED).
{ pose proof (st_ok_mem_ok rsegs _ _ _ HS0) as (_ & HRs & _).
  cbn [ss_mem ms_mem restrict] in HRs.
  apply Forall_cons_iff in HRs as [HR0 _].
  unfold region_ok in HR0.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR0.
  rewrite U2 in HR0. destruct HR0 as (_ & _ & _ & HCs).
  rewrite Forall_forall in HCs.
  unfold HP_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  lazymatch goal with
  | |- val_mem _ ?m (_ + ?off) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?r))) =>
    let n := eval vm_compute in (Z.to_nat r) in
    apply (val_of_chunk_ok rsegs E0 m (hx_sp x) off 8%N (SOff n 0)
      (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 r))));
    [ apply HCs; cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite hk_sv_SOff0; subst E0;
      rewrite (ew_Ereg_nat (hx_regs x) (@nil word) n (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
      symmetry; apply Z_to_bv_bv_unsigned
    | apply bv_unsigned_in_range
    | cbn [Z.of_N]; lia ]
  end. }
assert (KEA : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - 0x120 <= a < hx_sp x) ->
   aview rsegs (w_H (hx_W x)) (ms_mem ms1) a = aview rsegs (w_H (hx_W x)) (hx_memc x) a).
{ refine (hgp_kept_run rsegs (fun a => hx_sp x - 0x120 <= a < hx_sp x) E0 (ss_mem ss_pbA)
    (w_H (hx_W x)) (hx_memc x) (hx_memc x) (ms_mem ms1) (fun a _ _ => eq_refl) HFr _).
  intros a (r & Hin & Hb). unfold ss_pbA, pbA_stk in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite U2 in Hb. lia. }
(* ---------------- the `fsd fs0,144(sp)` by hand ---------------- *)
rreg HS0 (2%bv : bv 5) R2.
assert (R2' : getr (ms_regs ms1) 2 = Z_to_bv 64 (hx_sp x - 256)).
{ rewrite R2. cbn [sv_denot]. rewrite U2. f_equal; lia. }
assert (Hsg : bv_signed (Z_to_bv 12 144) = 144) by (vm_compute; reflexivity).
pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E0 _ _ HS0 eq_refl) as Hshape.
cbn [ss_pc] in Hshape. rewrite Hshape.
eapply (hgp_fsd rsegs B pb_segs_low pb_wx) with
  (tbl := pb_tbl) (p := PF_FSD) (q := PF_FSD + 4) (wz := 0x08813827)
  (rs1 := 2%bv) (rs2 := 8%bv) (imm := Z_to_bv 12 144)
  (base := hx_sp x - 256) (a := hx_sp x - 112)
  (STK := hx_STK x) (sp0 := hx_sp0 x) (FP := hx_FP x) (ly := hx_ly x) (S := hx_S x)
  (W0 := hx_W0 x) (mem0 := hx_mem0 x) (md0 := hx_md0 x) (own := hx_own x)
  (lyc := hx_lyc x) (Sc := hx_Sc x) (k := hx_k x).
- exact pb_tbl_ok.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_refl_bv.
- reflexivity.
- exact R2'.
- rewrite Hsg. lia.
- lia.
- lia.
- exact HJ0.
- intros i Hi. apply Hpres1. lia.
- intros i Hi. left. lia.
- intros mem2 md2 Hout2 Hvm2 HJ2 Hio2 Hpr2.
  (* ---------------- chunk B: the realign, the .got word, the frame header, the hole ---------------- *)
  assert (Hpres2 : forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) mem2 a)
    by (intros a Ha; apply Hpr2; apply Hpres1; exact Ha).
  assert (Hm32 : exists m, hx_spa x = 32 * m)
    by (apply Z.mod_divide in ST9 as [m Hm]; [exists m; lia | lia]).
  destruct Hm32 as [m Hm].
  assert (Hfr8 : hx_fr x / 8 = 4 * m + 8).
  { rewrite ST11, Hm. replace (32 * m + 64) with ((4 * m + 8) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hshfv : hx_shf x = SHADOW_OFF + (4 * m + 8))
    by (unfold hx_shf, shadow_addr; rewrite Hfr8; reflexivity).
  assert (Hmlo : 2 ^ 41 <= m) by lia.
  assert (Hmhi : m <= 2 ^ 42) by lia.
  assert (Hstk : hstack_ok (hx_lyc x) (hx_fr x) PAT_KEY).
  { unfold hstack_ok. change (Z.of_nat (length PAT_KEY)) with 8.
    split; [exact FW3|]. split; [cbn; lia|]. split; [lia|]. split; [lia|].
    unfold PAT_KEY. repeat apply Forall_cons; try apply Forall_nil; lia. }
  set (E1 := Ereg (ms_regs ms1) [w64 SHADOW_OFF; w64 (hx_spa x); w64 (hx_shf x)]).
  assert (E12 : ew E1 2 = Z_to_bv 64 (hx_sp x - 256))
    by (subst E1; rewrite (ew_Ereg_nat (ms_regs ms1) _ 2 2%bv eq_refl); exact R2').
  assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (subst E1; exact (ew_Ereg_extra (ms_regs ms1) _ 0)).
  assert (E133 : ew E1 33 = Z_to_bv 64 (hx_spa x)) by (subst E1; exact (ew_Ereg_extra (ms_regs ms1) _ 1)).
  assert (E134 : ew E1 34 = Z_to_bv 64 (hx_shf x)) by (subst E1; exact (ew_Ereg_extra (ms_regs ms1) _ 2)).
  assert (U12 : bv_unsigned (ew E1 2) = hx_sp x - 256) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (U132 : bv_unsigned (ew E1 32) = SHADOW_OFF)
    by (rewrite E132; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U133 : bv_unsigned (ew E1 33) = hx_spa x) by (rewrite E133; apply unsigned_lit_small; lia).
  assert (U134 : bv_unsigned (ew E1 34) = hx_shf x)
    by (rewrite E134; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  assert (HS1 : st_ok rsegs E1 ss_pbB
    (restrict (w_H (hx_W x)) (@mkst fx (ms_regs ms1) (Z_to_bv 64 PF_B) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_pbB. subst E1. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute; reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil.
      + unfold pbB_fr, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U133. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable rsegs). apply Hpres2. lia.
      + unfold pbB_hole, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U134. unfold SHADOW_OFF in *.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable rsegs).
        destruct (hole_raw_zero rsegs B pb_segs_low (hx_lyc x) (hx_Sc x) (hx_W x) mem2 md2
          (hx_fr x) PAT_KEY (proj1 HJ2) Hstk (Z_to_bv 64 (hx_shf x + o))
          ltac:(apply in_hU; rewrite unsigned_lit_small by lia;
                change (Z.of_nat (length PAT_KEY)) with 8; unfold hx_shf in *; lia)) as [Hh Hb].
        split; [exact Hh | exists (Z_to_bv 8 0); exact Hb].
      + unfold pbB_got, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [unfold PB_GOT_SH; lia|]. split; [unfold PB_GOT_SH; lia|].
        split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ 0 PB_GOT_SH 8 (SLit PB_SH_CELL) PB_SH_CELL);
          [reflexivity | unfold PB_SH_CELL; zside | zside |].
        rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kgot).
      + unfold pbB_cell, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [unfold PB_SH_CELL; lia|]. split; [unfold PB_SH_CELL; lia|].
        split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ 0 PB_SH_CELL 8 (SOff 32 0) SHADOW_OFF);
          [rewrite hk_sv_SOff0; exact E132 | unfold SHADOW_OFF; zside | zside |].
        rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kcell).
    - apply pairwise_disjoint_of_extents.
      unfold pbB_fr, pbB_hole, pbB_got, pbB_cell, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
      rewrite U133, U134.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold PB_GOT_SH, PB_SH_CELL, SHADOW_OFF in *. repeat split; lia.
    - unfold pbB_facts. split.
      + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U12, U132, U133, U134.
        change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
        change (2 ^ 0) with 1. rewrite Z.mod_1_r.
        repeat split; try (unfold SHADOW_OFF in *; lia).
        all: first
          [ rewrite Zminus_mod, ST7; reflexivity
          | exact ST9
          | rewrite Hshfv; replace (SHADOW_OFF + (4 * m + 8)) with (4 * (536862720 + m + 2))
              by (unfold SHADOW_OFF; lia); apply Z.mod_mul; lia ].
      + cbn [f_conds f_alias conds_ok alias_ok]. split; [exact I|].
        unfold pbB_al1, pbB_al2. cbn [fst snd].
        split; [|split; [|exact I]].
        * apply U_inj. rewrite U_SAlu, U_SLit.
          rewrite (U_atom _ 2%nat (hx_sp x - 256) E12 ltac:(lia)).
          rewrite (U_atom _ 33%nat (hx_spa x) E133 ltac:(lia)).
          cbn [zalu_raw].
          replace (zcanon (-32)) with (2 ^ 64 - 32) by (vm_compute; reflexivity).
          rewrite (pbF_land_m32 (hx_sp x - 256) ltac:(lia)).
          unfold hx_spa, hx_sp in *. rewrite !hd_land32.
          pose proof (Z.div_mod (spZ (hx_regs x) - 256) 32 ltac:(lia)).
          pose proof (Z.mod_pos_bound (spZ (hx_regs x) - 256) 32 ltac:(lia)).
          change 0x100 with 256. apply zcanon_id. unfold M64. lia.
        * apply U_inj. rewrite U_SAlu, U_SAlu, U_SLit.
          rewrite (U_atom_off _ 33%nat (hx_spa x) 64 E133 ltac:(lia) ltac:(lia)).
          rewrite (U_atom _ 32%nat SHADOW_OFF E132 ltac:(unfold SHADOW_OFF; lia)).
          rewrite (U_atom _ 34%nat (hx_shf x) E134 ltac:(unfold SHADOW_OFF in *; lia)).
          cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
          rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
          rewrite (zcanon_id ((hx_spa x + 64) / 8)) by (unfold M64; split; [apply Z.div_pos; lia|];
            apply Z.div_lt_upper_bound; lia).
          rewrite Hshfv. replace (hx_spa x + 64) with (hx_fr x) by lia. rewrite Hfr8.
          replace (4 * m + 8 + SHADOW_OFF) with (SHADOW_OFF + (4 * m + 8)) by lia.
          apply zcanon_id. unfold M64, SHADOW_OFF in *. lia. }
  (* the hole: the plain journal becomes the cut-state form at PAT_ZERO, the eight stores write PAT_KEY *)
  assert (Hstk0 : hstack_ok (hx_lyc x) (hx_fr x) PAT_ZERO).
  { unfold hstack_ok. change (Z.of_nat (length PAT_ZERO)) with 8.
    split; [exact FW3|]. split; [cbn; lia|]. split; [lia|]. split; [lia|].
    unfold PAT_ZERO. repeat apply Forall_cons; try apply Forall_nil; lia. }
  assert (HH0 : hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x)
     (hx_md0 x) (hx_own x) (hx_lyc x) (hx_Sc x) (hx_W x) mem2 md2 (hx_k x) (hx_fr x) PAT_ZERO)
    by (first [ apply (hj_enter0 rsegs B pb_segs_low); [exact HJ2 | exact Hstk0]
              | apply (hj_enter0 rsegs B); [exact HJ2 | exact Hstk0] ]).
  assert (HJ2U : ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x)
     (hx_md0 x) (hx_own x) (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x)).
  { rewrite <- (hU_len (hx_fr x) PAT_KEY PAT_ZERO eq_refl). exact (proj1 HH0). }
  replace (PF_FSD + 4) with PF_B by (vm_compute; reflexivity).
  aj_run_toH pb_tbl_ok HS1 HJ2U PC_RES.
  { eapply (awr_okH_cons_gen _ _ _ _ _ _ _ _ _ _ _ 33%nat (hx_spa x));
      [reflexivity | exact U133 | unfold pbB_fr; cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; left; lia |].
    eapply (awr_okH_cons_hole _ _ _ _ _ _ _ _ _ _ (hx_fr x) PAT_KEY 34%nat);
      [reflexivity | exact U134 | unfold pbB_hole; cbn [YP09.r_wlo]; lia
      | unfold pbB_hole; cbn [YP09.r_whi]; change (Z.of_nat (length PAT_KEY)) with 8; lia |].
    apply awr_okH_cons_ro; [unfold pbB_got; cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_okH_cons_ro; [unfold pbB_cell; cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_okH_nil. }
  lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
  assert (HK0 : forall r : bv 5, In r [(3%bv : bv 5); 4%bv; 10%bv; 11%bv; 12%bv; 13%bv] ->
     getr (ms_regs ms1) r = getr (hx_regs x) r).
  { intros r Hr. refine (regs_kept_of_st_ok rsegs E0 _ _ (hx_regs x) (@nil word) _ HS0 _ _ r Hr).
    - apply env_agree_refl.
    - vm_compute; reflexivity. }
  (* the hole's bytes at the end of chunk B *)
  assert (Hpat3 : hpat rsegs (hx_W x) (ms_mem ms3) (hx_fr x) PAT_KEY).
  { pose proof (st_ok_mem_ok rsegs _ _ _ HS1) as (_ & HRs3 & _).
    cbn [ss_mem ms_mem restrict] in HRs3.
    apply Forall_cons_iff in HRs3 as [_ HRs3]. apply Forall_cons_iff in HRs3 as [HRh _].
    unfold region_ok in HRh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRh.
    rewrite U134 in HRh. destruct HRh as (_ & _ & _ & HCh).
    cbn [YP09.r_chunks] in HCh.
    repeat (let H1 := fresh "HCk" in apply Forall_cons_iff in HCh; destruct HCh as [H1 HCh]).
    intros i Hi. change (Z.of_nat (length PAT_KEY)) with 8 in Hi.
    replace (shadow_addr (hx_fr x)) with (hx_shf x) by reflexivity.
    assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by (clear - Hi; lia).
    destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk2); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk1); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk0); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk6); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk5); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk4); reflexivity.
    - rewrite (pbF_chunk_byte _ _ _ _ _ _ HCk3); reflexivity. }
  (* the write windows of chunk B *)
  lazymatch goal with H : frame_of _ _ (mrestrict _ mem2) (mrestrict _ _) |- _ => rename H into HFRB end.
  assert (WB : forall b, in_wrange E1 (ss_mem ss_pbB) b ->
     (hx_spa x + 64 <= b < hx_spa x + 88) \/ hp_hole x b).
  { intros b (r & Hin & Hb). unfold ss_pbB in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      unfold pbB_fr, pbB_hole, pbB_got, pbB_cell in Hb;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
    - rewrite U133 in Hb. left. lia.
    - rewrite U134 in Hb. right. unfold hp_hole. lia.
    - lia.
    - lia. }
  (* every byte outside the parse's stack window and outside the hole is as at the call *)
  assert (KEB : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
     aview rsegs (w_H (hx_W x)) (ms_mem ms3) a = aview rsegs (w_H (hx_W x)) (hx_memc x) a).
  { intros a Ha H1 H2.
    rewrite (hgp_kept_run rsegs (fun b => (hx_sp x - T_parse_STK <= b < hx_sp x) \/ hp_hole x b)
      E1 (ss_mem ss_pbB) (w_H (hx_W x)) mem2 mem2 (ms_mem ms3) (fun b _ _ => eq_refl) HFRB
      ltac:(intros b Hb; destruct (WB b Hb) as [HH|HH]; [left; unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia | right; exact HH]) a Ha
      ltac:(intros [HH|HH]; [exact (H1 HH) | exact (H2 HH)])).
    rewrite (hgp_kept_of_eq rsegs (fun b => hx_sp x - 112 <= b < hx_sp x - 104)
      (w_H (hx_W x)) (ms_mem ms1) mem2 ltac:(intros y Hy; cbv beta in Hy; apply Hout2; unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia) a Ha ltac:(cbv beta; unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)).
    exact (KEA a Ha ltac:(unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)). }
  (* the saves and fs0 are still in the frame *)
  assert (KSV : forall a, hx_sp x - 112 <= a < hx_sp x - 104 \/ hx_sp x - 104 <= a < hx_sp x ->
     aview rsegs (w_H (hx_W x)) (ms_mem ms3) a = aview rsegs (w_H (hx_W x)) mem2 a).
  { intros a Ha.
    exact (hgp_kept_run rsegs (fun b => (hx_spa x + 64 <= b < hx_spa x + 88) \/ hp_hole x b)
      E1 (ss_mem ss_pbB) (w_H (hx_W x)) mem2 mem2 (ms_mem ms3) (fun b _ _ => eq_refl) HFRB WB a
      ltac:(lia) ltac:(intros [HH|HH]; [lia | unfold hp_hole in HH; rewrite Hshfv in HH; unfold SHADOW_OFF in *; lia])). }
  assert (HSV3 : hp_saved_ok x (ms_mem ms3)).
  { split.
    - rewrite Forall_forall in HSV0 |- *. intros cc Hcc.
      apply (hgp_val_mem_kept rsegs _ (ms_mem ms1) (ms_mem ms3) _ 8 _ (HSV0 cc Hcc)).
      intros i Hi.
      assert (Hin : hx_sp x - 104 <= hx_sp x + fst cc + i < hx_sp x)
        by (unfold HP_SAVED in Hcc; cbn [In] in Hcc;
            destruct Hcc as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]]]]];
            cbn [fst]; lia).
      rewrite (KSV _ ltac:(right; exact Hin)).
      exact (hgp_kept_of_eq rsegs (fun b => hx_sp x - 112 <= b < hx_sp x - 104)
        (w_H (hx_W x)) (ms_mem ms1) mem2 ltac:(intros y Hy; cbv beta in Hy; apply Hout2; unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia) (hx_sp x + fst cc + i) ltac:(lia) ltac:(cbv beta; lia)).
    - apply (hgp_val_mem_kept rsegs _ mem2 (ms_mem ms3) _ 8 _ Hvm2).
      intros i Hi. apply KSV. left. unfold HP_FS0. lia. }
  (* presence over the caller's window *)
  assert (HPR3 : forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) (ms_mem ms3) a).
  { pose proof HJ2U as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
    intros a Ha.
    refine (proj1 (hp_apresent_unp (w_H (hx_W x)) (hU (hx_fr x) PAT_KEY) (ms_mem ms3) a _) (Hp a Ha)).
    apply in_hU_false. rewrite unsigned_lit_small by lia.
    change (Z.of_nat (length PAT_KEY)) with 8. unfold hx_shf, shadow_addr, SHADOW_OFF in *. lia. }
  (* the registers at the cut *)
  rreg HS1 (2%bv : bv 5) Q2. rreg HS1 (8%bv : bv 5) Q8. rreg HS1 (3%bv : bv 5) Q3.
  rreg HS1 (4%bv : bv 5) Q4. rreg HS1 (9%bv : bv 5) Q9. rreg HS1 (18%bv : bv 5) Q18.
  rreg HS1 (19%bv : bv 5) Q19. rreg HS1 (26%bv : bv 5) Q26. rreg HS1 (27%bv : bv 5) Q27.
  rreg HS1 (10%bv : bv 5) Q10.
  assert (EW : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr (ms_regs ms1) r)
    by (intros n r Hn; subst E1; exact (ew_Ereg_nat (ms_regs ms1) _ n r Hn)).
  pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E1 _ _ HS1 eq_refl) as Hshape3.
  cbn [ss_pc] in Hshape3. rewrite Hshape3.
  lazymatch goal with |- SRr ?sg ?W (mkCfg (mkst ?rg _ ?mm _) ?md) ?Q =>
    change (SRr sg W (cfg_at rsegs PC_RES rg mm md) Q) end.
  apply HK. unfold pbE_mid.
  split.
  { eapply hj_repat_raw.
    - exact HJ2U.
    - exact Hstk.
    - reflexivity.
    - unfold PAT_KEY. repeat apply Forall_cons; try apply Forall_nil; lia.
    - exact Hpat3. }
  split.
  { eapply same_io_trans; [|apply same_io_materialized; apply same_but_materialized_wvb_any].
    eapply same_io_trans; [|exact Hio2].
    apply same_io_materialized; apply same_but_materialized_wvb_any. }
  split; [exact KEB|].
  split; [exact HSV3|].
  split; [exact HPR3|].
  split.
  + unfold hk_cregs.
    split; [rewrite Q2; exact E133|].
    split; [rewrite Q8, U12; f_equal; lia|].
    split; [rewrite Q3, (EW 3%nat 3%bv eq_refl);
            apply HK0; cbn [In]; repeat (first [left; reflexivity | right])|].
    split; [rewrite Q4, (EW 4%nat 4%bv eq_refl);
            apply HK0; cbn [In]; repeat (first [left; reflexivity | right])|].
    split; [rewrite Q9, (EW 13%nat 13%bv eq_refl),
              (HK0 (13%bv : bv 5) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact H13|].
    split; [rewrite Q18, (EW 12%nat 12%bv eq_refl),
              (HK0 (12%bv : bv 5) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact H12|].
    split; [rewrite Q19, (EW 11%nat 11%bv eq_refl),
              (HK0 (11%bv : bv 5) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact H11|].
    split; [rewrite Q26; exact E134|].
    rewrite Q27. exact E132.
  + rewrite Q10, (EW 10%nat 10%bv eq_refl),
      (HK0 (10%bv : bv 5) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact H10.
Qed.

(* ---------------------------------- from the open to the end ---------------------------------- *)
Lemma pbE_core0_of_mid : forall x regs mem md, call_ok B x -> pbE_mid x regs mem md ->
pbE_core0 B x regs mem md.
Proof.
intros x regs mem md Hc Hm.
pose proof Hm as (HJ & Hio & HK & HSV & HPR & HCR & _).
unfold pbE_core0.
split; [exact HJ|]. split; [exact Hio|]. split; [exact HK|]. split; [exact HSV|].
split; [exact (hgh_errno_kept B x mem errno_low Hc HK)|].
split; [exact (hgh_res_present B x PAT_KEY mem md Hc HJ HPR) | exact HCR].
Qed.

Lemma pbE_mid_ok : forall x : ctx, call_ok B x -> EPI_ok B MT x -> (forall r n, FIND_ok B MT x r n) ->
forall regs mem md, pbE_mid x regs mem md ->
SRr rsegs (hx_W x) (cfg_at rsegs PC_RES regs mem md) (PPOST B MT x).
Proof.
intros x Hc HE HF regs mem md Hm.
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
replace (cfg_at rsegs PC_RES regs mem md)
  with (cfg_at (fx := mkFP (@fp_regs fx) (@fp_csr fx)) rsegs PC_RES regs mem md)
  by (rewrite hgh_fx_eta; reflexivity).
apply (pbE_res_ok x Hc HE HF (@fp_regs fx) (@fp_csr fx) regs mem md).
split; [exact (pbE_core0_of_mid x regs mem md Hc Hm)|].
split; [split; [intros k _; reflexivity | exact Hfrm]|].
pose proof Hm as (_ & _ & _ & _ & _ & _ & H10). exact H10.
Qed.

(* ======================================= segment E ======================================= *)
Theorem segE_ok : segE_stmt B MT.
Proof.
intros x Hc HE HF. apply (pbF_entry x Hc). exact (pbE_mid_ok x Hc HE HF).
Qed.

End c.

Check segE_ok.
Print Assumptions segE_ok.
