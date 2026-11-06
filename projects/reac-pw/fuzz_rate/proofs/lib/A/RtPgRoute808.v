(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its unstripped
   twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, whose loaded bytes are the pinned
   image's): ONE instrumented 1-byte check of the walk of LLVMFuzzerTestOneInput (0x80714), the check at 0x808f0.
   Proves no function (kind: segment lemma of the entry function's walk).

   THE CODE
     0x808e8  srli a0,s9,3        0x808ec  add a0,a0,s2        0x808f0  lb a0,0(a0)
     0x808f4  beqz a0,+8 -> 0x808fc                            0x808f8  j 0x83090
     0x83090  andi a1,s9,7        0x83094  bge a1,a0,+8 -> 0x8309c (the error path)
     0x83098  j 0x808fc           0x808fc  lbu a5,0(s9)  (the input byte; this lemma stops BEFORE it)
   s9 = p is the input pointer (an allocator block start, so 8-aligned) and s2 = SHADOW_OFF. The byte loaded at
   0x808f0 is the metadata byte of p at (p >> 3) + SHADOW_OFF; the check passes when it is 0 or when p mod 8 is
   below it, which saddr_ok gives. The error path is not reached.

   WHY THIS SHAPE (the region route). The token path of lib/Reusable/YCbn.v (tok_load / tok_branch) does not cover
   this branch form: at 0x808f4 the not-equal successor 0x808f8 is a `j`, not the `andi` of a slow block, so
   tok_branch takes its None arm and asks for shadow 0 over the WHOLE eight-byte granule of p, which is false when
   p's granule is the input's last and partial one. Instead the metadata byte is carried as a one-byte REGION of the
   symbolic state, based on an extra atom whose value is shadow_of_addr SHADOW_OFF p, with the alias fact
   ((s9 >> 3) + s2, that atom) and the atom facts "p is 8-aligned" and "the byte is in [0, 7]". Then sym_step_sh
   resolves the address of the `lb` to that region BEFORE sym_step_tok ever offers it to tok_load, the load is an
   ordinary region load, and no shadow obligation is raised at all. The `beqz` and the slow block's `bge` are split
   with the engine's branch split, and the error arm of the `bge` dies by saddr_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ============================== the code table and the engine's parameters ============================== *)
(* 0x808e8 .. 0x808fc and the out-of-line slow block 0x83090 .. 0x83098 *)
Definition rtr_tbl : ctable := build_table rsegs 0x83090 4 (build_table rsegs 0x808e8 6 TEmpty).
Lemma rtr_tbl_ok : table_ok rsegs rtr_tbl.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.
Lemma rtr_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* s2 (x18) holds SHADOW_OFF, so the shadow base is its own atom; no block shadow entry is used. *)
Definition RTRBx : sv := SOff 18 0.
Definition RTRspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* atom 25 = s9 = p (8-aligned, in the allocator's range); atom 33 = the metadata byte, in [0, 7];
   atom 32 = the address of that byte, declared equal to (s9 >> 3) + s2 *)
Definition rtr_facts : facts :=
  mkFacts [(25%nat, mkAF 4096 0x800000000000 3); (33%nat, mkAF 0 7 0)] []
          [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0), SOff 32 0)].
Definition rtr_mem : smem := [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]].
(* the registers the two live arms may change: a0 (x10) and a1 (x11) *)
Definition RTR_KEEP : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

(* ============================== small facts about one byte and one cell ============================== *)
Lemma rtr_le_byte_1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

(* saddr_ok at an 8-aligned address: the byte is 0 or strictly between 0 and 8 *)
Lemma rtr_sok_range : forall p s, p mod 8 = 0 -> saddr_ok p s -> 0 <= s <= 7.
Proof. intros p s Hp [->|[H1 H2]]; [lia|]. rewrite Hp in H1. lia. Qed.
Lemma rtr_sok_pos : forall p s, p mod 8 = 0 -> saddr_ok p s -> s <> 0 -> 0 < s.
Proof. intros p s Hp [->|[H1 H2]] Hs; [lia|]. rewrite Hp in H1. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rtr_aview_val1 : forall H mem x v,
aview rsegs H mem x = Some v -> val_mem rsegs (mrestrict H mem) x 1 v /\ 0 <= v < 256.
Proof.
intros H mem x v A. unfold aview in A.
destruct (mbyte rsegs (mrestrict H mem) x) as [b|] eqn:Eb; [|discriminate A].
cbn [option_map] in A. injection A as <-. pose proof (u8_range b) as R. split; [|exact R].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
rewrite Z.add_0_r, Eb, rtr_le_byte_1 by exact R. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* A one-byte read-only region at the address held by atom k, holding the byte s. *)
Lemma rtr_cell_region : forall E H mem (k : nat) sa s e,
bv_unsigned (ew E k) = sa -> aview rsegs H mem sa = Some s -> sv_denot E e = Z_to_bv 64 s ->
0 <= sa -> sa < 2 ^ 64 ->
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 e)]).
Proof.
intros E H mem k sa s e Hk A He H0 H1. destruct (rtr_aview_val1 _ _ _ _ A) as [V R].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hk. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. apply (chunk_ok_val rsegs E _ sa 0 1 e s He); [cbn; lia | lia |].
rewrite Z.add_0_r. exact V.
Qed.

(* Every register but a0 and a1 holds its entry value when the symbolic state keeps it as its own atom. *)
Lemma rtr_keep_regs : forall E ss ms regs extra,
st_ok rsegs E ss ms -> env_agree 32 (Ereg regs extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) RTR_KEEP = true ->
forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs extra HS HA Hf r H10 H11.
destruct (Z.eq_dec (bv_unsigned r) 0) as [Hr0 | Hr0].
{ assert (Er : r = (0%bv : bv 5)) by (apply bv_eq; rewrite Hr0; vm_compute; reflexivity).
  subst r. unfold getr. rewrite bv_eqb_refl. reflexivity. }
apply (regs_kept_of_st_ok rsegs E ss ms regs extra RTR_KEEP HS HA Hf r).
pose proof (u5_range r) as Hu.
rewrite <- (Z_to_bv_bv_unsigned 5 r).
assert (Hc : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/
bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/ bv_unsigned r = 16 \/
bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
repeat match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd|Hd] end;
rewrite Hc; cbv [RTR_KEEP]; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* ============================== the step ============================== *)
Definition rtr_ss : sstate := mkSS 0x808e8 sr_atoms rtr_mem None rtr_facts.

(* The walk reaches 0x808fc, the load of the input byte, with every register but a0 and a1 as at 0x808e8, the same
   memory and the same model up to materialization. *)
Lemma rtr_A_808f0_step : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) p s,
getr regs (Z_to_bv 5 25) = w64 p ->
getr regs (Z_to_bv 5 18) = w64 SHADOW_OFF ->
p mod 8 = 0 -> 4096 <= p -> p + 8 <= kHighMemEnd ->
aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some s ->
saddr_ok p s ->
(forall regs' md',
   (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr regs' r = getr regs r) ->
   same_but_materialized md md' ->
   SRr rsegs W (cfg_at rsegs 0x808fc regs' mem md') Q) ->
SRr rsegs W (cfg_at rsegs 0x808e8 regs mem md) Q.
Proof.
intros W regs mem md Q p s H25 H18 Hal Hlo Hhi Hav Hok K.
pose proof rtr_wx as Hwx.
pose proof (rtr_sok_range p s Hal Hok) as Hs7.
unfold kHighMemEnd in Hhi.
set (extra := [Z_to_bv 64 (shadow_of_addr SHADOW_OFF p); Z_to_bv 64 s]).
set (E := Ereg regs extra).
assert (Ew25 : ew E 25%nat = Z_to_bv 64 p).
{ unfold E. rewrite (ew_Ereg_nat regs extra 25%nat (Z_to_bv 5 25) eq_refl), H25. reflexivity. }
assert (Ew18 : ew E 18%nat = Z_to_bv 64 SHADOW_OFF).
{ unfold E. rewrite (ew_Ereg_nat regs extra 18%nat (Z_to_bv 5 18) eq_refl), H18. reflexivity. }
assert (Ew32 : ew E 32%nat = Z_to_bv 64 (SHADOW_OFF + p / 8)) by reflexivity.
assert (Ew33 : ew E 33%nat = Z_to_bv 64 s) by reflexivity.
assert (HG : facts_ok E rtr_facts).
{ unfold facts_ok. split; [|split].
  - cbv [rtr_facts f_atoms]. cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew25, unsigned_lit_small by lia.
      change (2 ^ 3) with 8. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - exact I.
  - cbv [rtr_facts f_alias]. cbn [alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 25%nat 18%nat 32%nat p SHADOW_OFF Ew25 ltac:(lia) Ew18 Ew32). }
assert (HS : st_ok rsegs E rtr_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x808e8) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rtr_cell_region E (w_H W) mem 32%nat (SHADOW_OFF + p / 8) s (SOff 33 0)).
    + rewrite Ew32. apply unsigned_lit_small. unfold SHADOW_OFF. split; [lia|].
      assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). lia.
    + unfold shadow_of_addr in Hav. exact Hav.
    + cbn [sv_denot]. rewrite Ew33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    + unfold SHADOW_OFF. lia.
    + unfold SHADOW_OFF. assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). lia.
  - cbv [rtr_ss rtr_mem]. cbn [ss_mem pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok rsegs RTRBx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs extra) E) by apply env_agree_refl.
unfold cfg_at. change (w64 0x808e8) with (Z_to_bv 64 0x808e8).
(* 0x808e8 .. 0x808f0, the region load, then the `beqz` *)
srr_run_tok rtr_tbl_ok HS SHOK RTRspan.
assert (Em1 : ms_mem ms = mem)
  by (apply (frame_of_read_only E (ss_mem rtr_ss) mem (ms_mem ms)); [vm_compute; reflexivity | exact HF]).
srr_branch_tok rtr_tbl_ok HS SHOK RTRspan.
- (* the byte is 0: the check passes at once *)
  srr_run_to_tok rtr_tbl_ok HS SHOK RTRspan 0x808fc.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms0 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems, Em2. apply K.
  + apply (rtr_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
  + apply with_vm_backing_same.
- (* the byte is not 0: the slow block, then its `bge` *)
  assert (Hs0 : s <> 0).
  { intros Hz. cbn [sv_denot] in Hc. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc by lia.
    rewrite Hz in Hc. vm_compute in Hc. discriminate. }
  pose proof (rtr_sok_pos p s Hal Hok Hs0) as Hspos.
  srr_run_tok rtr_tbl_ok HS SHOK RTRspan.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  srr_branch_tok rtr_tbl_ok HS SHOK RTRspan.
  + (* the error path: p mod 8 >= the byte, which saddr_ok refuses *)
    exfalso. cbv [branch_taken] in Hc0. cbn [sv_denot] in Hc0.
    rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc0 by lia.
    rewrite YCbn.bv_lts_small in Hc0 by lia.
    apply negb_true_iff in Hc0. apply Z.ltb_nlt in Hc0. lia.
  + (* the check passes: back to 0x808fc *)
    srr_run_to_tok rtr_tbl_ok HS SHOK RTRspan 0x808fc.
    assert (Em3 : ms_mem ms1 = mem)
      by (rewrite <- Em2; refine (frame_of_read_only E _ _ _ _ HF1); vm_compute; reflexivity).
    pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms1 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    rewrite Ems, Em3. apply K.
    * apply (rtr_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
    * apply with_vm_backing_same.
Qed.

End b.

Print Assumptions rtr_A_808f0_step.
