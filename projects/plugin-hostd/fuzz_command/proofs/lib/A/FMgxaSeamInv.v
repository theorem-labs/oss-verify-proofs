(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamInv.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Can the seam DERIVE GXA's store invariant from the harness state?  No; this file proves it.

   GXA's musl-vfprintf statement takes `mem_inv img_segs m` (lib/CJ/RL/GXA/VfprintfCall.v:37;
   Mem.mem_inv, lib/CJ/Lib/Mem.v:88) over m = cjstore (w_H W) mem = mrestrict (w_H W) mem.  This
   file is why the seam's contract (FMsnprintfSx.v sh_avfprintf_icpt_realizesUx) carries no store
   premise and the seam runs GXA on the normalized store instead (FMgxaSeamNorm.v).  ARU and
   ecall_preU (FMupoison.v:32,44) cannot give it, because no clause of theirs reads the store itself:
   - AR (YG0n.v:490) reads memory through the view aview segs (w_H W) mem (ARm, YG0n.v:205-225)
     and through ahs (YG0n.v:449), which asks bytes to be PRESENT (ahs_pres) or to hold 0 (ahz);
     ALedger (YG0n.v:311), abudget_ok (YG0n.v:388) and amwf (YG0n.v:437) do not mention memory;
   - the view lays the image under the store (mbyte, YP09.v:18): a store byte equal to the image
     byte does not change it, and a store byte where the image has none only adds to it;
   - ecall_pre (YG0d.v:278) adds presence on the stack (apresent); ecall_preU adds upoison_ok, which
     does not mention memory, and upoisoned, a view fact;
   - the world's two laws on its hidden set are w_Hoff = H_off_segments (YA0n.v:23, YK04.v:38), which
     hides only addresses outside every segment, so the restricted store keeps every image address,
     and w_H8 (YA0n.v:25), which makes w_H constant on each 8-byte-aligned shadow-band word; neither
     stops w_H from hiding nothing.
   So every premise survives store_ext (ecall_preU_ext_store): add store bytes only where the store
   has none, each the image byte or where the image has none, and hide less.  On fm.asan's image two
   such changes break the two halves of mem_inv:
   (1) rom_fill: fill the store with the image bytes.  The byte at 0x10000 (.rodata, a segment that
       is not writable) is then in the store (ro_ok_not_derivable).
   (2) world_open + poke0: hide nothing and put a byte at 2^47, outside every segment
       (lim_ok_not_derivable).
   Each theorem says: if the clause followed from ecall_preU, no state would satisfy ecall_preU.  The
   same holds for ARU, for the whole mem_inv, and for FMgxaSeamBase's store_cleanU, which implies
   mem_inv. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFupoison.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import FMgxaSeamBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the two halves of mem_inv ---- *)
Definition mem_ro_ok (segs : list Segment) (m : word -> option byte) : Prop :=
  forall a b, m a = Some b -> Mem.ro_addr segs a = false.
Definition mem_lim_ok (segs : list Segment) (m : word -> option byte) : Prop :=
  forall a b, m a = Some b -> find_segment segs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE.

Lemma mem_inv_split : forall segs m, Mem.mem_inv segs m <-> mem_ro_ok segs m /\ mem_lim_ok segs m.
Proof.
intros segs m. split.
- intros H. split; intros a b E; destruct (Mem.mem_inv_elim segs m a b H E) as [R L]; assumption.
- intros [R L]. apply Mem.mem_inv_intro. intros a b E. exact (conj (R a b E) (L a b E)).
Qed.

(* ---- the store changes the premises cannot see ---- *)
(* m' adds to m only bytes where m has none, each the image byte or where the image has none *)
Definition store_ext (segs : list Segment) (m m' : word -> option byte) : Prop :=
  forall w, m' w = m w \/ (m w = None /\ (m' w = YK11.seg_rom segs w \/ YK11.seg_rom segs w = None)).

(* the store with every image byte filled in *)
Definition rom_fill (segs : list Segment) (m : word -> option byte) : word -> option byte :=
  fun w => match m w with Some b => Some b | None => YK11.seg_rom segs w end.

(* the store with a 0 byte at x, if it has none there *)
Definition poke0 (m : word -> option byte) (x : word) : word -> option byte :=
  fun w => match m w with
           | Some b => Some b
           | None => if Z.eqb (bv_unsigned w) (bv_unsigned x) then Some (Z_to_bv 8 0) else None
           end.

Lemma H_off_open : forall segs, H_off_segments segs (fun _ : word => false).
Proof. intros segs a E. exact (False_ind _ (diff_false_true E)). Qed.

(* the world that hides nothing (fuzz_manifest's text: the fifth argument is the w_H8 field, trivial for the empty map) *)
Definition world_open {segs : list Segment} (W : world segs) : world segs :=
  mkW segs (fun _ => false) (w_A W) (H_off_open segs) (w_Awf W) (fun _ _ => eq_refl).

Lemma store_ext_some : forall segs m m' w b, store_ext segs m m' -> m w = Some b -> m' w = Some b.
Proof.
intros segs m m' w b X E. destruct (X w) as [R|[R _]]; [rewrite R; exact E | rewrite E in R; discriminate R].
Qed.

Lemma store_ext_keep : forall segs m m' w, store_ext segs m m' -> m w <> None -> m' w <> None.
Proof.
intros segs m m' w X N. destruct (m w) as [b|] eqn:E; [|contradiction].
rewrite (store_ext_some segs m m' w b X E). discriminate.
Qed.

Lemma store_ext_rom_fill : forall segs m, store_ext segs m (rom_fill segs m).
Proof.
intros segs m w. unfold rom_fill.
destruct (m w) as [b|]; [left; reflexivity | right; split; [reflexivity | left; reflexivity]].
Qed.

Lemma store_ext_poke0 : forall segs m x, YK11.seg_rom segs x = None -> store_ext segs m (poke0 m x).
Proof.
intros segs m x Hx w. unfold poke0. destruct (m w) as [b|]; [left; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned w) (bv_unsigned x)) as [Q|Q].
- right. split; [reflexivity|]. right. assert (w = x) as -> by (apply bv_eq; exact Q). exact Hx.
- left. reflexivity.
Qed.

(* ---- every premise survives store_ext ---- *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma aview_ext_store : forall (H H' : word -> bool) m m',
  H_off_segments segs H -> hsub H' H -> store_ext segs m m' -> rd_ext (aview segs H m) (aview segs H' m').
Proof.
intros H H' m m' Hoff Hs X a v. unfold aview, mbyte, mrestrict.
destruct (H (Z_to_bv 64 a)) eqn:E.
- unfold YK11.seg_rom. rewrite (memory_read1_hidden segs H Hoff _ E). cbn. discriminate.
- destruct (H' (Z_to_bv 64 a)) eqn:E'; [rewrite (Hs _ E') in E; discriminate|].
  destruct (X (Z_to_bv 64 a)) as [R|[R0 [R|R]]].
  + rewrite R. exact (fun Hv => Hv).
  + rewrite R, R0. destruct (YK11.seg_rom segs (Z_to_bv 64 a)); exact (fun Hv => Hv).
  + rewrite R0, R. cbn. discriminate.
Qed.

Lemma AR_ext_store : forall ly S (W W' : world segs) mem mem' md,
  hsub (w_H W') (w_H W) -> w_A W' = w_A W -> store_ext segs mem mem' ->
  AR segs B ly S W mem md -> AR segs B ly S W' mem' md.
Proof.
intros ly S W W' mem mem' md Hs HA X (M & L & BO & MW & HP & HZ).
split; [eapply ARm_ext; [exact (aview_ext_store (w_H W) (w_H W') mem mem' (w_Hoff W) Hs X) | exact M]|].
split; [exact L|].
split; [unfold abudget_ok in *; rewrite HA; exact BO|].
split; [exact MW|].
split.
- intros a Ha NC Hh. refine (store_ext_keep segs mem mem' _ X _).
  destruct Hh as [Hh|Hv]; [exact (HP a Ha NC (or_introl (Hs _ Hh))) | exact (HP a Ha NC (or_intror Hv))].
- intros g Hg Ha HF. exact (store_ext_some segs mem mem' _ _ X (HZ g Hg Ha HF)).
Qed.

Lemma ecall_pre_ext_store : forall ly S (W W' : world segs) regs mem mem' md,
  hsub (w_H W') (w_H W) -> w_A W' = w_A W -> store_ext segs mem mem' ->
  ecall_pre segs B ly S W regs mem md -> ecall_pre segs B ly S W' regs mem' md.
Proof.
intros ly S W W' regs mem mem' md Hs HA X (HAR & R1 & R2 & R3 & R4 & HP & R5 & R6).
refine (conj (AR_ext_store ly S W W' mem mem' md Hs HA X HAR)
          (conj R1 (conj R2 (conj R3 (conj R4 (conj _ (conj R5 R6))))))).
intros a Ha. destruct (HP a Ha) as [Hh [b Hb]]. split.
- destruct (w_H W' (Z_to_bv 64 a)) eqn:E; [rewrite (Hs _ E) in Hh; discriminate Hh | reflexivity].
- exists b. exact (store_ext_some segs mem mem' _ _ X Hb).
Qed.

Lemma unpoison_ext_store : forall U m m', store_ext segs m m' -> store_ext segs (unpoison U m) (unpoison U m').
Proof.
intros U m m' X w. unfold unpoison. destruct (in_ush U (bv_unsigned w)); [left; reflexivity | exact (X w)].
Qed.

Lemma ecall_preU_ext_store : forall ly S U (W W' : world segs) regs mem mem' md,
  hsub (w_H W') (w_H W) -> w_A W' = w_A W -> store_ext segs mem mem' ->
  ecall_preU segs B ly S U W regs mem md -> ecall_preU segs B ly S U W' regs mem' md.
Proof.
intros ly S U W W' regs mem mem' md Hs HA X (HE & OK & UP).
split; [exact (ecall_pre_ext_store ly S W W' regs _ _ md Hs HA (unpoison_ext_store U mem mem' X) HE)|].
split; [exact OK|].
intros s Hs'. exact (aview_ext_store (w_H W) (w_H W') mem mem' (w_Hoff W) Hs X s 247 (UP s Hs')).
Qed.

Lemma ARU_ext_store : forall ly S U (W W' : world segs) mem mem' md,
  hsub (w_H W') (w_H W) -> w_A W' = w_A W -> store_ext segs mem mem' ->
  ARU segs B ly S U W mem md -> ARU segs B ly S U W' mem' md.
Proof.
intros ly S U W W' mem mem' md Hs HA X (HR & OK & UP).
split; [exact (AR_ext_store ly S W W' _ _ md Hs HA (unpoison_ext_store U mem mem' X) HR)|].
split; [exact OK|].
intros s Hs'. exact (aview_ext_store (w_H W) (w_H W') mem mem' (w_Hoff W) Hs X s 247 (UP s Hs')).
Qed.

Lemma hsub_world_open : forall (W : world segs), hsub (w_H (world_open W)) (w_H W).
Proof. intros W a E. exact (False_ind _ (diff_false_true E)). Qed.

(* the world hides no image address *)
Lemma seg_vis : forall (W : world segs) a, find_segment segs (bv_unsigned a) 1 <> None -> w_H W a = false.
Proof. intros W a Hs. destruct (w_H W a) eqn:E; [exfalso; exact (Hs (w_Hoff W a E)) | reflexivity]. Qed.

Lemma ro_addr_seg : forall a, Mem.ro_addr segs a = true -> find_segment segs (bv_unsigned a) 1 <> None.
Proof. intros a H E. unfold Mem.ro_addr in H. rewrite E in H. discriminate H. Qed.

End g.

(* ---- fm.asan's two witnesses ---- *)
(* .rodata's first byte: segment 0 = [0x10000, 0x30000), not writable (FMsnprintfGt.v:34 rom_seg0) *)
Definition RO_WIT : word := Z_to_bv 64 0x10000.
(* the user address limit 2^47 = TASK_SIZE, outside every segment *)
Definition LIM_WIT : word := Z_to_bv 64 (2 ^ 47).

Lemma ro_wit_ro : Mem.ro_addr tfibsegs RO_WIT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ro_wit_img : match YK11.seg_rom tfibsegs RO_WIT with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lim_wit_out : find_segment tfibsegs (bv_unsigned LIM_WIT) 1 = None.
Proof. vm_compute. reflexivity. Qed.
Lemma lim_wit_img : YK11.seg_rom tfibsegs LIM_WIT = None.
Proof. vm_compute. reflexivity. Qed.
Lemma lim_wit_hi : (bv_unsigned LIM_WIT <? TASK_SIZE) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma rom_fill_ro_byte : forall (W : world tfibsegs) mem,
  cjstore (w_H W) (rom_fill tfibsegs mem) RO_WIT <> None.
Proof.
intros W mem. unfold cjstore, mrestrict.
rewrite (seg_vis tfibsegs W RO_WIT (ro_addr_seg tfibsegs RO_WIT ro_wit_ro)).
unfold rom_fill. cbv beta iota.
destruct (mem RO_WIT) as [b|]; cbv beta iota; [discriminate|].
pose proof ro_wit_img as Hs. revert Hs.
destruct (YK11.seg_rom tfibsegs RO_WIT); cbv beta iota; [intros _; discriminate | intros Hs; discriminate Hs].
Qed.

Lemma rom_fill_not_ro_ok : forall (W : world tfibsegs) mem,
  ~ mem_ro_ok tfibsegs (cjstore (w_H W) (rom_fill tfibsegs mem)).
Proof.
intros W mem HR. pose proof (rom_fill_ro_byte W mem) as Hb.
destruct (cjstore (w_H W) (rom_fill tfibsegs mem) RO_WIT) as [b|] eqn:E; [|exact (Hb eq_refl)].
pose proof (HR RO_WIT b E) as Hf. rewrite ro_wit_ro in Hf. discriminate Hf.
Qed.

Lemma poke_lim_byte : forall (W : world tfibsegs) mem,
  cjstore (w_H (world_open W)) (poke0 mem LIM_WIT) LIM_WIT <> None.
Proof.
intros W mem.
change (cjstore (w_H (world_open W)) (poke0 mem LIM_WIT) LIM_WIT) with (poke0 mem LIM_WIT LIM_WIT).
unfold poke0. destruct (mem LIM_WIT) as [b|]; cbv beta iota; [discriminate|].
rewrite Z.eqb_refl. cbv beta iota. discriminate.
Qed.

Lemma poke_not_lim_ok : forall (W : world tfibsegs) mem,
  ~ mem_lim_ok tfibsegs (cjstore (w_H (world_open W)) (poke0 mem LIM_WIT)).
Proof.
intros W mem HL. pose proof (poke_lim_byte W mem) as Hb.
destruct (cjstore (w_H (world_open W)) (poke0 mem LIM_WIT) LIM_WIT) as [b|] eqn:E; [|exact (Hb eq_refl)].
destruct (HL LIM_WIT b E) as [Hs|Hl]; [exact (Hs lim_wit_out)|].
pose proof lim_wit_hi as Hh. apply Z.ltb_ge in Hh. lia.
Qed.

(* ---- the answer ---- *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* (1) a state of ecall_preU whose store holds a read-only byte *)
Theorem ecall_preU_rom_fill : forall ly S U (W : world tfibsegs) regs mem md,
  ecall_preU tfibsegs B ly S U W regs mem md ->
  ecall_preU tfibsegs B ly S U W regs (rom_fill tfibsegs mem) md /\
  ~ Mem.mem_inv tfibsegs (cjstore (w_H W) (rom_fill tfibsegs mem)).
Proof.
intros ly S U W regs mem md HE. split.
- exact (ecall_preU_ext_store tfibsegs B ly S U W W regs mem _ md (hsub_refl _) eq_refl
           (store_ext_rom_fill tfibsegs mem) HE).
- intros HI. exact (rom_fill_not_ro_ok W mem (proj1 (proj1 (mem_inv_split _ _) HI))).
Qed.

(* (2) a state of ecall_preU whose store holds a byte at 2^47, outside every segment *)
Theorem ecall_preU_poke_lim : forall ly S U (W : world tfibsegs) regs mem md,
  ecall_preU tfibsegs B ly S U W regs mem md ->
  ecall_preU tfibsegs B ly S U (world_open W) regs (poke0 mem LIM_WIT) md /\
  ~ mem_lim_ok tfibsegs (cjstore (w_H (world_open W)) (poke0 mem LIM_WIT)).
Proof.
intros ly S U W regs mem md HE. split.
- exact (ecall_preU_ext_store tfibsegs B ly S U W (world_open W) regs mem _ md (hsub_world_open tfibsegs W)
           eq_refl (store_ext_poke0 tfibsegs mem LIM_WIT lim_wit_img) HE).
- exact (poke_not_lim_ok W mem).
Qed.

Theorem ro_ok_not_derivable :
  (forall ly S U (W : world tfibsegs) regs mem md, ecall_preU tfibsegs B ly S U W regs mem md ->
     mem_ro_ok tfibsegs (cjstore (w_H W) mem)) ->
  forall ly S U (W : world tfibsegs) regs mem md, ~ ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros D ly S U W regs mem md HE.
destruct (ecall_preU_rom_fill ly S U W regs mem md HE) as [HE' _].
exact (rom_fill_not_ro_ok W mem (D ly S U W regs _ md HE')).
Qed.

Theorem lim_ok_not_derivable :
  (forall ly S U (W : world tfibsegs) regs mem md, ecall_preU tfibsegs B ly S U W regs mem md ->
     mem_lim_ok tfibsegs (cjstore (w_H W) mem)) ->
  forall ly S U (W : world tfibsegs) regs mem md, ~ ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros D ly S U W regs mem md HE.
destruct (ecall_preU_poke_lim ly S U W regs mem md HE) as [HE' HN].
exact (HN (D ly S U (world_open W) regs _ md HE')).
Qed.

Theorem mem_inv_not_derivable :
  (forall ly S U (W : world tfibsegs) regs mem md, ecall_preU tfibsegs B ly S U W regs mem md ->
     Mem.mem_inv tfibsegs (cjstore (w_H W) mem)) ->
  forall ly S U (W : world tfibsegs) regs mem md, ~ ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros D. apply ro_ok_not_derivable. intros ly S U W regs mem md HE.
exact (proj1 (proj1 (mem_inv_split _ _) (D ly S U W regs mem md HE))).
Qed.

Theorem store_clean_not_derivable :
  (forall ly S U (W : world tfibsegs) regs mem md, ecall_preU tfibsegs B ly S U W regs mem md ->
     store_cleanU (w_H W) mem) ->
  forall ly S U (W : world tfibsegs) regs mem md, ~ ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros D. apply mem_inv_not_derivable. intros ly S U W regs mem md HE.
exact (mem_inv_of_store_clean (w_H W) mem (D ly S U W regs mem md HE)).
Qed.

(* the same over ARU alone *)
Theorem ro_ok_not_derivable_ARU :
  (forall ly S U (W : world tfibsegs) mem md, ARU tfibsegs B ly S U W mem md ->
     mem_ro_ok tfibsegs (cjstore (w_H W) mem)) ->
  forall ly S U (W : world tfibsegs) mem md, ~ ARU tfibsegs B ly S U W mem md.
Proof.
intros D ly S U W mem md HA.
pose proof (ARU_ext_store tfibsegs B ly S U W W mem _ md (hsub_refl _) eq_refl
              (store_ext_rom_fill tfibsegs mem) HA) as HA'.
exact (rom_fill_not_ro_ok W mem (D ly S U W _ md HA')).
Qed.

Theorem lim_ok_not_derivable_ARU :
  (forall ly S U (W : world tfibsegs) mem md, ARU tfibsegs B ly S U W mem md ->
     mem_lim_ok tfibsegs (cjstore (w_H W) mem)) ->
  forall ly S U (W : world tfibsegs) mem md, ~ ARU tfibsegs B ly S U W mem md.
Proof.
intros D ly S U W mem md HA.
pose proof (ARU_ext_store tfibsegs B ly S U W (world_open W) mem _ md (hsub_world_open tfibsegs W) eq_refl
              (store_ext_poke0 tfibsegs mem LIM_WIT lim_wit_img) HA) as HA'.
exact (poke_not_lim_ok W mem (D ly S U (world_open W) _ md HA')).
Qed.

End i.
