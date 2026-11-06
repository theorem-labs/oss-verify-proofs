(* Contracts of memory-checking runtime functions in the form that holds where the runtime's own invariant AR no longer
   holds: at process exit, after the module destructor asan.module_dtor (X2, lib/A/AE37.v) has rewritten the shadow of
   every global. The facts these contracts use are plain memory facts: the stack window present, the cells the code
   reads holding their values, the bytes of the destination writable. Each contract here is the AR contract of
   lib/Reusable/YG0d.v (or of lib/A/AE3h.v) with AR dropped from the premise and from the post, and with the facts AR
   gave replaced by premises of their own.
   - aecall_pre_noar K: what `ecall_pre` (YG0d.v) says minus AR, with the stack named by its own bounds and a window
     of K bytes below the stack pointer;
   - acells_ok m l: every cell of the list l (base, size, [(offset, width, value)]) holds its value in m;
   - aintrin_noar_realizes op cells K pc: `aintrin_realizes` (YG0d.v) in that form, for a function that reads the
     cells `cells`; its post also keeps every byte the shadow map hides (hs_kept, lib/A/AE2y.v), which is what lets
     the AR contract be derived from it (lib/A/AE31.v);
   - xret_realizes_noar_vals pc xw xv xpre: `xret_realizes_noar` (lib/A/AE3h.v) with the value of every byte it
     writes stated: after the call, each byte a with xw a reads xv a. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From Stdlib Require Import Sorting.Mergesort Sorting.Permutation Structures.Orders.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The chunks of a region, sorted by offset, so that a region whose chunks together hold zero over [lo, hi) can be
   checked by one pass (zcover) instead of one search per byte. *)
Module ChunkOff <: Orders.TotalLeBool.
  Definition t := YP09.chunk.
  Definition leb (x y : t) : bool := Z.leb (YP09.c_off x) (YP09.c_off y).
  Lemma leb_total : forall x y, leb x y = true \/ leb y x = true.
  Proof. intros x y. unfold leb. destruct (Z.le_ge_cases (YP09.c_off x) (YP09.c_off y)); [left | right]; apply Z.leb_le; lia. Qed.
End ChunkOff.
Module ChunkSort := Mergesort.Sort ChunkOff.

Definition sv_zero (v : sv) : bool := match v with SLit z => Z.eqb z 0 | _ => false end.
Definition zval (cv : YP09.cval) : bool :=
  match cv with YP09.CVal _ v => sv_zero v | YP09.CZero _ => true | _ => false end.
(* zcover pos hi cs: going through cs in order, every byte of [pos, hi) lies in a chunk that holds zero. *)
Fixpoint zcover (pos hi : Z) (cs : list YP09.chunk) : bool :=
  match cs with
  | [] => Z.leb hi pos
  | c :: cs' => Z.leb (YP09.c_off c) pos && zval (YP09.c_val c) &&
                zcover (Z.max pos (YP09.c_off c + YP09.c_len c)) hi cs'
  end.

Lemma zval_byte : forall segs E base cv i, zval cv = true -> YP09.cbyte segs E base cv i = Some (Z_to_bv 8 0).
Proof.
  intros segs E base cv i Hz. destruct cv as [w v | l | l | dd s l]; cbn [zval] in Hz; try discriminate Hz; [|reflexivity].
  destruct v; cbn [sv_zero] in Hz; try discriminate Hz.
  match goal with H : (?zz =? 0) = true |- _ => apply Z.eqb_eq in H; subst zz end.
  cbn [YP09.cbyte sv_denot]. unfold YP09.byte_of_word.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma zcover_sound : forall segs E m base cs pos hi,
  zcover pos hi cs = true -> Forall (YP09.chunk_ok segs E m base) cs ->
  forall a, pos <= a < hi -> YP09.mbyte segs m (base + a) = Some (Z_to_bv 8 0).
Proof.
  intros segs E m base cs. induction cs as [|c cs IH]; intros pos hi Hz Hok a Ha; cbn [zcover] in Hz.
  - apply Z.leb_le in Hz. lia.
  - apply andb_prop in Hz as [Hz Hrest]. apply andb_prop in Hz as [Hoff Hv]. apply Z.leb_le in Hoff.
    inversion Hok as [|? ? Hc Hok']; subst.
    destruct (Z_lt_le_dec a (YP09.c_off c + YP09.c_len c)) as [Hin|Hout].
    + destruct (Hc (a - YP09.c_off c) ltac:(lia)) as (b & Hb & Hm).
      rewrite (zval_byte segs E _ _ _ Hv) in Hb. injection Hb as <-.
      replace (base + a) with (base + YP09.c_off c + (a - YP09.c_off c)) by lia. exact Hm.
    + apply (IH _ hi Hrest Hok'). lia.
Qed.

Lemma region_zero : forall segs E m r,
  YP09.region_ok segs E m r -> YP09.r_base r = None ->
  zcover (YP09.r_lo r) (YP09.r_hi r) (ChunkSort.sort (YP09.r_chunks r)) = true ->
  forall a, YP09.r_lo r <= a < YP09.r_hi r -> YP09.mbyte segs m a = Some (Z_to_bv 8 0).
Proof.
  intros segs E m r Hr Hb Hz a Ha. unfold YP09.region_ok in Hr. cbv zeta in Hr. destruct Hr as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [YP09.base_val] in Hcs.
  assert (Hs : Forall (YP09.chunk_ok segs E m 0) (ChunkSort.sort (YP09.r_chunks r))).
  { apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) Hcs).
    eapply Permutation_in; [apply Permutation_sym, ChunkSort.Permuted_sort | exact Hc]. }
  rewrite <- (Z.add_0_l a). exact (zcover_sound segs E m 0 _ _ _ Hz Hs a Ha).
Qed.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Definition aecall_pre_noar (K : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  YK0s.ret_ok (getr regs 1) /\
  spZ regs mod 16 = 0 /\ kHighMemBeg + K <= spZ regs /\ spZ regs <= 2 ^ 47 /\
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

Definition acells_ok (m : word -> option byte) (l : list (Z * Z * list (Z * N * Z))) : Prop :=
  Forall (fun r => Forall (fun c => val_mem segs m (fst (fst r) + fst (fst c)) (N.to_nat (snd (fst c))) (snd c)) (snd r)) l.

(* The cells of l are in range and their values fit their widths: then acells_ok turns them into the regions a symbolic
   run reads (the same regions AE2y.rodata_ok builds from AR's const cells). *)
Definition rodata_bounds (l : list (Z * Z * list (Z * N * Z))) : bool :=
  forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
    forallb (fun c => (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r)) l.
Lemma cells_regions_ok : forall l m E, rodata_bounds l = true -> acells_ok m l ->
  Forall (YP09.region_ok segs E m) (map ro_region l).
Proof.
  intros l m E Hb Hc. unfold rodata_bounds in Hb. rewrite forallb_forall in Hb. unfold acells_ok in Hc.
  apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
  specialize (Hb _ Hin). pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as Hcs. cbn [fst snd] in Hb, Hcs.
  apply andb_prop in Hb as [Hb Hbs]. apply andb_prop in Hb as [H0 Hhi]. apply Z.leb_le in H0. apply Z.leb_le in Hhi.
  unfold ro_region, YP09.region_ok.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
  rewrite forallb_forall in Hbs. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
  specialize (Hbs _ Hc'). pose proof (proj1 (Forall_forall _ _) Hcs _ Hc') as Hv. cbn [fst snd] in Hbs, Hv.
  apply andb_prop in Hbs as [Hbs H4]. apply andb_prop in Hbs as [H2 H3].
  apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
  unfold ro_chunk. cbn [fst snd].
  eapply (chunk_ok_val segs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
  rewrite Z.add_0_l. exact Hv.
Qed.

Definition aintrin_noar_realizes (op : memop) (cells : list (Z * Z * list (Z * N * Z))) (K pc : Z) : Prop :=
  forall W regs mem md d x n,
  aecall_pre_noar K W regs mem ->
  acells_ok (mrestrict (w_H W) mem) cells ->
  getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  (forall a, d <= a < d + n -> writable_at segs (mrestrict (w_H W) mem) a /\ ~ (spZ regs - K <= a < spZ regs)) ->
  amem_range d n ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
  (match op with
   | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\
       (forall a, x <= a < x + n -> aview segs (w_H W) mem a <> None /\ ~ (spZ regs - K <= a < spZ regs)) /\
       (d + n <= x \/ x + n <= d) /\ amem_range x n /\
       range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\
       (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
   | OSet => True end) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 d /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
          match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - K <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       hs_kept (w_H W) mem mem').

Definition xret_realizes_noar_vals (pc : Z) (xw : Z -> Prop) (xv : Z -> Z)
  (xpre : world segs -> (word -> option byte) -> Prop) : Prop :=
  forall ly S (W : world segs) regs mem md,
  ecall_pre segs B ly S W regs mem md -> xpre W mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ xw a ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ xw a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, xw a -> aview segs (w_H W) mem' a = Some (xv a))).

End x.
