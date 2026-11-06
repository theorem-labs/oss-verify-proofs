(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "unit"; "option"; "prod"; "Some"; "andb"; "nil"; "None"; "pair"; "true"; "nat"; "negb"; "false"; "tt"; "app"; "snd"; "fst"; "list"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "bind"; "astate"; "op"; "ret"; "ameta"; "Free"; "M"; "st_metas"; "st_bounces"; "mslot"; "st_active"; "st_avail_meta_area_count"; "st_regions"; "st_seq"; "mkA"; "st_avail_meta_count"; "st_unmap_seq"; "st_usage"; "Malloc"; "st_area_head"; "st_areas"; "st_avail_meta"; "st_avail_meta_areas"; "st_brk"; "st_free_meta_head"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_area_tail"; "st_init_done"; "UNIT"; "modify"; "get"; "PGSZ"; "am_last"; "am_avail"; "frame"; "znth"; "am_sc"; "fail"; "region"; "setm"; "slotst"; "srun"; "am_freed"; "getm"; "FModel"; "am_aidx"; "am_maplen"; "am_next"; "ask"; "mkAMeta"; "am_mem"; "am_slots"; "failure"; "osptr_eqb"; "IB"; "SP"; "am_prev"; "mkRegion"; "ones"; "padd"; "IRet"; "class_size"; "get_head"; "get_links"; "massert"; "mkRun"; "mkSlot"; "mlookup"; "nth_slot"; "set_head"; "set_links"; "usage_of"; "RkMap"; "am_set_avail"; "bounce_idx"; "brkst"; "fkind"; "fr_off"; "headloc"; "outcome"; "page_round"; "rg_len"; "set_avail_meta_area_count"; "set_avail_meta_areas"; "ss_fr"; "stride_of"; "upd_region"; "zset"; "HActive"; "lowbit"; "lupd"; "new_region"; "put"; "set_brk"; "setslot"; "size_classes"; "ss_hdr"; "upd_slot"; "BrkCur"; "FAssert"; "FUser"; "HFreeMeta"; "IAsk"; "KBrkGrow"; "KMunmap"; "MFree"; "MUsed"; "NEST_FUEL"; "RkBrk"; "am_set_freed"; "dequeue"; "enframe"; "find_frame_in"; "irun"; "is_bouncing"; "kreq"; "mupdate"; "poff"; "queue"; "set_avail_meta"; "set_avail_meta_count"; "set_bounces"; "set_metas"; "set_next"; "set_prev"; "set_regions"; "set_seq"; "set_unmap_seq"; "slot_start"; "sr_trace"; "AREA_HDR"; "BrkDead"; "BrkNever"; "FFuel"; "KBrkQuery"; "KGuard"; "KJunk"; "KMmapNone"; "KMmapRW"; "KMprotect"; "METAS_PER_AREA"; "META_SIZE"; "MMAP_THRESHOLD"; "MRaw"; "RkMetaRes"; "activate_group"; "alloc_meta"; "alloc_slot"; "am_set_aidx"; "am_set_links"; "am_set_slots"; "area_from_brk"; "area_from_mmap"; "askz"; "bit"; "class_of_units"; "clz32"; "ctz32"; "decay_bounces"; "dequeue_head"; "find_frame"; "fr_kind"; "fr_n"; "free"; "halve_while_big"; "halve_while_even"; "init_state"; "links_of"; "malloc"; "mcheck"; "med_cnt_tab"; "mkFrame"; "nontrivial_free"; "open_area"; "prid"; "release_slot"; "rg_kind"; "rg_live"; "rg_rw"; "run_op"; "run_script"; "set_active"; "set_area_head"; "set_area_tail"; "set_areas"; "set_free_meta_head"; "set_init_done"; "set_meta_alloc_shift"; "set_mmap_counter"; "set_usage"; "set_usage_of"; "size_overflows"; "size_to_class"; "slot_junk"; "slot_zero"; "small_cnt"; "small_cnt_tab"; "span_loop"; "sptr_eqb"; "sr_ans"; "sr_err"; "sr_ptrs"; "sr_state"; "step_seq"; "with_links"; "zupd"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "mul"; "sub"; "ltb"; "leb"; "land"; "to_nat"; "div"; "lor"; "shiftr"; "even"; "modulo"; "pow";
"ldiff"; "shiftl"; "@Corelib.Lists.ListDef"; "nth"; "repeat"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "fold_left"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition UNIT : Z := 16.
Definition IB : Z := 4.
Definition PGSZ : Z := 4096.
Definition MMAP_THRESHOLD : Z := 131052.
Definition METAS_PER_AREA : Z := 101.
Definition META_SIZE : Z := 40.
Definition AREA_HDR : Z := 24.

Definition size_classes : list Z := ltac2:(tb__ "0|0|
S2S0Z1S2S0Z2S2S0Z3S2S0Z4S2S0Z5S2S0Z6S2S0Z7S2S0Z8S2S0Z9S2S0ZaS2S0ZcS2S0ZfS2S0Z12S2S0Z14S2S0Z19S2S0Z1fS2S0Z24S2S0Z2aS2S0Z32S2S0Z3fS2S0Z48S2S0Z54S2S0Z66S2S0Z7fS2S0Z92S2S0ZaaS2S0ZccS2S0ZffS2S0Z124S2S0Z154S2S0Z199S2S0Z1ffS2S0Z248S2S0Z2aaS2S0Z332S2S0Z3ffS2S0Z491S2S0Z554S2S0Z665S2S0Z7ffS2S0Z924S2S0ZaaaS2S0ZcccS2S0ZfffS2S0Z1248S2S0Z1554S2S0Z1998S2S0Z1fffS8S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition small_cnt_tab : list (list Z) := ltac2:(tb__ "0|8|
S2S13S0A1M0S2S0Z1eM1S2S0G1S2S0G1S8S0A1M2A3A3A3S2G0S2S0Z1fM3S2S0ZfM4S2S0G4G2A3A3A3S2G0S2S0Z14S2S0ZaM5S2S0G5G2A3A3A3S2G0S2S0G3S2S0G4S2S0Z7G2A3A3A3M6S2G0S2S0Z19S2S0ZcS2S0Z6G2A3M7A3A3S2G0S2S0Z15S2S0G5S2S0Z5G2A3A3A3S2G0S2S0Z12S2S0Z8S2S0Z4G2A3A3A3S2G0G6S2G0S2S0Z1cS2S0ZeG7A3A3S8G0A1A3A3A3A3A3A3A3A3A3").

Definition med_cnt_tab : list Z := ltac2:(tb__ "0|0|
S2S0Z1cS2S0Z18S2S0Z14S2S0Z20S8S0A1A3A3A3A3").

Definition znth (i : Z) (l : list Z) : Z := nth (Z.to_nat i) l 0.

Fixpoint zupd (l : list Z) (i : nat) (v : Z) : list Z :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S i' => h :: zupd t i' v
  end.
Definition zset (i : Z) (v : Z) (l : list Z) : list Z := ltac2:(tb__ "0|0|
Se5Vl;SedVi;A1Vv;A3").

Definition class_size (sc : Z) : Z := ltac2:(tb__ "0|0|
Se8S34S3bVsc;S77A2A2").

Definition lowbit (m : Z) : Z := Z.land m (- m).
Definition ctz32 (m : Z) : Z := Z.log2 (lowbit m).
Definition clz32 (x : Z) : Z := 31 - Z.log2 x.

Definition ones (k : Z) : Z := ltac2:(tb__ "0|1|
Se9Sf3Z2Se6Vk;Z1M0A2A2G0A2").
Definition bit (k : Z) : Z := 2 ^ k.

Definition page_round (x : Z) : Z := ltac2:(tb__ "0|0|
Se8SeeSe9Se6Vx;S37A2Z1A2S37A2S37A2").

Definition class_of_units (k : Z) : Z := ltac2:(tb__ "0|3|
S1S0L_;M0SeaVk;ZaA2Vk;Se6Vk;Z1M1A2S0Se6Se8Se9Z1cSb4R1A1A2Z4A2Z8A2S0G0SeaS3bSe6R1G1A2M2S77A2R2A2Se6R1Z2A2R1X1x2S0G0SeaS3bR1S77A2R3A2G2R1X1x2Ti;Ti;Tk;X1x2").

Definition size_to_class (n : Z) : Z := ltac2:(tb__ "0|0|
Sb3Sf0Se9Se6Vn;S4eA2Z1A2Z4A2A1").

Definition size_overflows (n : Z) : bool := 2 ^ 63 - 4097 <=? n.

Inductive sptr := SP (r : nat) (off : Z).

Definition sptr_eqb (p q : sptr) : bool := ltac2:(tb__ "0|0|
S16S1Lp;Vp;ScS0S16S1Lq;Vq;ScS0S7Sf8R4R2A2Se7R3R1A2A2Lo';Lr';X16x1Lo;Lr;X16x1").
Definition osptr_eqb (p q : option sptr) : bool := ltac2:(tb__ "0|2|
S4S16A1M0S1Lp;Vp;S16G0S1Lq;M1Vq;S16SdeR2R1A2Lq;SeX4x2Lp;G1Vq;S16SeLs;SbX4x2X4x2").
Definition padd (p : sptr) (d : Z) : sptr := ltac2:(tb__ "0|0|
S16S16Lp;Vp;ScS0S4fR2Se6R1Vd;A2A2Lo;Lr;X16x1").
Definition prid (p : sptr) : nat := match p with SP r _ => r end.
Definition poff (p : sptr) : Z := match p with SP _ o => o end.

Inductive rkind :=
| RkBrk
| RkMetaRes
| RkMap.

Record region := mkRegion {
  rg_kind : rkind;
  rg_len  : Z;
  rg_rw   : list Z;
  rg_live : bool
}.

Inductive kreq :=
| KBrkQuery
| KBrkGrow (npages : Z)
| KGuard
| KMmapRW (len : Z)
| KMmapNone (len : Z)
| KMprotect (page : sptr)
| KMunmap (r : nat) (len : Z)
| KJunk (pristine : Z).

Inductive failure :=
| FAssert (site : Z)
| FFuel
| FModel (tag : Z).

Inductive itree (S A : Type) : Type :=
| IRet (a : A)
| IAsk (q : kreq) (snap : S) (k : Z -> itree S A)
| IFail (f : failure).
Arguments IRet {S A}. Arguments IAsk {S A}. Arguments IFail {S A}.

Fixpoint ibind {S A B : Type} (t : itree S A) (k : A -> itree S B) : itree S B :=
  match t with
  | IRet a => k a
  | IAsk q snap c => IAsk q snap (fun b => ibind (c b) k)
  | IFail f => IFail f
  end.

Inductive fkind := FUser | FGroup.

Record frame := mkFrame {
  fr_off  : Z;
  fr_n    : Z;
  fr_kind : fkind
}.

Record slotst := mkSlot { ss_hdr : option (Z * Z); ss_fr : option frame }.

Definition slot_zero : slotst := ltac2:(tb__ "0|1|
S5aS6S5S0S0A2SaS0S0Z0M0G0A4A2S9S3aA1A2").
Definition slot_junk : slotst := mkSlot None None.

Record ameta := mkAMeta {
  am_prev   : option sptr;
  am_next   : option sptr;
  am_mem    : sptr;
  am_avail  : Z;
  am_freed  : Z;
  am_last   : Z;
  am_sc     : Z;
  am_maplen : Z;
  am_aidx   : Z;
  am_slots  : list slotst

}.

Inductive mslot :=
| MFree (prev next : option sptr)
| MRaw
| MUsed (m : ameta).

Inductive brkst :=
| BrkNever
| BrkDead
| BrkCur (r : nat) (pages : Z).

Record astate := mkA {

  st_init_done : bool;
  st_mmap_counter : Z;
  st_free_meta_head : option sptr;
  st_avail_meta : sptr;
  st_avail_meta_count : Z;
  st_avail_meta_area_count : Z;
  st_meta_alloc_shift : Z;
  st_area_head : option sptr;
  st_area_tail : option sptr;
  st_avail_meta_areas : sptr;
  st_active : list (option sptr);
  st_usage : list Z;
  st_unmap_seq : list Z;
  st_bounces : list Z;
  st_seq : Z;
  st_brk : brkst;

  st_metas : list (sptr * mslot);
  st_regions : list region;
  st_areas : list sptr
}.

Definition init_state : astate := ltac2:(tb__ "0|5|
S25SeZ0M0S9S16A1M1S4fU0G0A2M2G0G0G0G1G1G2Sf7S4S16A1G1U30M3A3Sf7S0G0G3A3Sf7S0G0U20A3M4G4G0S9cS8S5S16S20A2A1S8S3eA1S8S16A1A13").

Definition M (A : Type) : Type := astate -> itree astate (A * astate).

Definition ret {A} (a : A) : M A := fun s => IRet (a, s).
Definition bind {A B} (m : M A) (k : A -> M B) : M B :=
  fun s => ibind (m s) (fun '(a, s') => k a s').
Definition fail {A} (f : failure) : M A := fun _ => IFail f.
Definition get : M astate := ltac2:(tb__ "0|0|
S18S54S18S5S18S18A2SaS18S18R1R1A4A3Ls;").
Definition put (s : astate) : M unit := ltac2:(tb__ "0|0|
S18S54S18S5S3S18A2SaS3S18SfVs;A4A3L_;").
Definition modify (f : astate -> astate) : M unit := ltac2:(tb__ "0|0|
S18S54S18S5S3S18A2SaS3S18SfVf;R1A1A4A3Ls;").
Definition askz (q : kreq) : M Z := ltac2:(tb__ "0|1|
S18S7eS18S5S0S18A2M0Vq;R1S0S54S18G0SaS0S18R1R2A4A3Lz;A5Ls;").

Definition ask (q : kreq) : M bool := ltac2:(tb__ "0|1|
S18S7eS18S5S1S18A2M0Vq;R1S0S54S18G0SaS1S18SdSe7R1Z0A2A1R2A4A3Lz;A5Ls;").
Definition massert (b : bool) (site : Z) : M unit := ltac2:(tb__ "0|0|
S1S1dS3A1Lb;Vb;S1aS3SfA2S3dS3S7bVsite;A1A2X1x2").

Definition mcheck (b : bool) (tag : Z) : M unit := ltac2:(tb__ "0|0|
S1S1dS3A1Lb;Vb;S1aS3SfA2S3dS3S44Vtag;A1A2X1x2").

Declare Scope mm_scope.
Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 100, m at next level, k at level 200, right associativity) : mm_scope.
Notation "m ;; k" := (bind m (fun _ => k))
  (at level 100, k at level 200, right associativity) : mm_scope.
Local Open Scope mm_scope.

Section Setters.
  Implicit Types (s : astate).
  Definition set_init_done (v : bool) s : astate := ltac2:(tb__ "0|0|
S25Vv;S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_mmap_counter (v : Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1Vv;S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_free_meta_head (v : option sptr) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1Vv;S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_avail_meta (v : sptr) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1Vv;S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_avail_meta_count (v : Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1Vv;S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_avail_meta_area_count (v : Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1Vv;S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_meta_alloc_shift (v : Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1Vv;S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_area_head (v : option sptr) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1Vv;S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_area_tail (v : option sptr) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1Vv;S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_avail_meta_areas (v : sptr) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1Vv;S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_active (v : list (option sptr)) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1Vv;S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_usage (v : list Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1Vv;S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_unmap_seq (v : list Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1Vv;S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_bounces (v : list Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1Vv;S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_seq (v : Z) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1Vv;S2eVs;A1S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_brk (v : brkst) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1Vv;S1eVs;A1S23Vs;A1S2bVs;A1A13").
  Definition set_metas (v : list (sptr * mslot)) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1Vv;S23Vs;A1S2bVs;A1A13").
  Definition set_regions (v : list region) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1Vv;S2bVs;A1A13").
  Definition set_areas (v : list sptr) s : astate := ltac2:(tb__ "0|0|
S25S33Vs;A1S31Vs;A1S2fVs;A1S2cVs;A1S26Vs;A1S22Vs;A1S30Vs;A1S2aVs;A1S32Vs;A1S2dVs;A1S21Vs;A1S28Vs;A1S27Vs;A1S1fVs;A1S24Vs;A1S2eVs;A1S1eVs;A1S23Vs;A1Vv;A13").
End Setters.

Fixpoint lupd {X : Type} (l : list X) (i : nat) (v : X) : list X :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S i' => h :: lupd t i' v
  end.

Fixpoint mlookup (l : list (sptr * mslot)) (p : sptr) : option mslot :=
  match l with
  | [] => None
  | (q, x) :: t => if sptr_eqb p q then Some x else mlookup t p
  end.
Fixpoint mupdate (l : list (sptr * mslot)) (p : sptr) (x : mslot) : list (sptr * mslot) :=
  match l with
  | [] => [(p, x)]
  | (q, y) :: t => if sptr_eqb p q then (q, x) :: t else (q, y) :: mupdate t p x
  end.

Definition getm (p : sptr) : M ameta := ltac2:(tb__ "0|3|
S17S18S1bS36S18S4S20A1S1dS1bA1M0Lx;S5bS1eR1A1Vp;A2S20S20G0Lm;R1S4S16A1M1G1S3dS1bS44Z1A1A2M2Lnext;Lprev;G2S1bS1aS1bR1A2Lam;X20x3Lm;G2X4x2Ls;A4").
Definition setm (p : sptr) (am : ameta) : M unit := ltac2:(tb__ "0|0|
S35S18S92S8cS1eR1A1Vp;S82Vam;A1A3R1A2Ls;A1").
Definition setslot (p : sptr) (x : mslot) : M unit := ltac2:(tb__ "0|0|
S35S18S92S8cS1eR1A1Vp;Vx;A3R1A2Ls;A1").

Definition am_set_links (pr nx : option sptr) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49Vpr;Vnx;S4aVm;A1S39Vm;A1S42Vm;A1S38Vm;A1S3cVm;A1S46Vm;A1S45Vm;A1S4bVm;A1Aa").
Definition am_set_prev (pr : option sptr) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49Vpr;S47Vm;A1S4aVm;A1S39Vm;A1S42Vm;A1S38Vm;A1S3cVm;A1S46Vm;A1S45Vm;A1S4bVm;A1Aa").
Definition am_set_next (nx : option sptr) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49S50Vm;A1Vnx;S4aVm;A1S39Vm;A1S42Vm;A1S38Vm;A1S3cVm;A1S46Vm;A1S45Vm;A1S4bVm;A1Aa").
Definition am_set_avail (v : Z) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49S50Vm;A1S47Vm;A1S4aVm;A1Vv;S42Vm;A1S38Vm;A1S3cVm;A1S46Vm;A1S45Vm;A1S4bVm;A1Aa").
Definition am_set_freed (v : Z) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49S50Vm;A1S47Vm;A1S4aVm;A1S39Vm;A1Vv;S38Vm;A1S3cVm;A1S46Vm;A1S45Vm;A1S4bVm;A1Aa").
Definition am_set_aidx (v : Z) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49S50Vm;A1S47Vm;A1S4aVm;A1S39Vm;A1S42Vm;A1S38Vm;A1S3cVm;A1S46Vm;A1Vv;S4bVm;A1Aa").
Definition am_set_slots (v : list slotst) (m : ameta) : ameta := ltac2:(tb__ "0|0|
S49S50Vm;A1S47Vm;A1S4aVm;A1S39Vm;A1S42Vm;A1S38Vm;A1S3cVm;A1S46Vm;A1S45Vm;A1Vv;Aa").

Definition links_of (x : mslot) : option sptr * option sptr := ltac2:(tb__ "0|2|
S20S5S4S16A1M0G0A2Lx;Vx;G0G0SaG0G0R2R1A4Lnx;Lpr;SaG0G0S9S16A1M1G1A4S1bSaG0G0S50R1A1S47R1A1A4Lam;X20x3").
Definition with_links (x : mslot) (pr nx : option sptr) : mslot := ltac2:(tb__ "0|2|
S20S20Lx;Vx;S4S16A1M0G0S81Vpr;Vnx;A2M1Lnext;Lprev;G1S1bS82SadVpr;Vnx;R1A3A1Lam;X20x3").

Definition get_links (p : sptr) : M (option sptr * option sptr) := ltac2:(tb__ "0|2|
S17S18S5S4S16A1M0G0A2M1S36S18S4S20A1S1dG1A1Lx;S5bS1eR1A1Vp;A2S20S1aG1SbfR1A1A2Lx;S3dG1S44Z2A1A2X4x2Ls;A4").
Definition set_links (p : sptr) (pr nx : option sptr) : M unit := ltac2:(tb__ "0|0|
S17S18S3S36S18S4S20A1S1dS3A1Lx;S5bS1eR1A1Vp;A2S20S76Vp;Se4R1Vpr;Vnx;A3A2Lx;S3dS3S44Z3A1A2X4x2Ls;A4").
Definition set_prev (p : sptr) (pr : option sptr) : M unit := ltac2:(tb__ "0|2|
S17S5S4S16A1M0G0A2M1S3S57Vp;A1G1S5eVp;Vpr;S11G0G0R1A3A3Ll;A4").
Definition set_next (p : sptr) (nx : option sptr) : M unit := ltac2:(tb__ "0|2|
S17S5S4S16A1M0G0A2M1S3S57Vp;A1G1S5eVp;S12G0G0R1A3Vnx;A3Ll;A4").

Inductive headloc := HActive (sc : Z) | HFreeMeta.

Definition get_head (h : headloc) : M (option sptr) := ltac2:(tb__ "0|1|
S17S18S4S16A1M0S36S18S66S1dG0A1Lh;Vh;S0S1aG0Sf6G0SedR1A1S21R2A1S9S16A1A4A2Lsc;S1aG0S2fR1A1A2X66x2Ls;A4").
Definition set_head (h : headloc) (v : option sptr) : M unit := ltac2:(tb__ "0|0|
S66S1dS3A1Lh;Vh;S0S35S18ScdS72S4S16A1S21R1A1SedR2A1Vv;A4R1A2Ls;A1Lsc;S35Sd1Vv;A1A1X66x2").

Definition queue (h : headloc) (m : sptr) : M unit := ltac2:(tb__ "0|6|
S17S5S4S16A1M0G0A2M1S3S57Vm;A1G1S17S3S3S58S7S4dS12G0G0R1A3M2S9S16A1M3A2S4dS11G0G0R1A3G3A2A2Z1A2S3S17G0S3S56Vh;A1G0G0S1dS3A1M4Lhd;R1S16S17G1S3S57R1A1G1G0G4Lx;G2S16S17S3S3S5eVm;S6S16R1A2S6S16R3A2A3S3S17S3S3S93R2S6S16Vm;A2M5A2S3S94R5G5A2L_;A4L_;A4Lhprev;S3dS3S44Z4A1A2X4x2Llh;A4Lhead;S17S3S3S5eVm;G5G5A3S3S5dVh;G5A2L_;A4X4x2Lhd;A4L_;A4Ll;A4").

Definition dequeue (h : headloc) (m : sptr) : M unit := ltac2:(tb__ "0|8|
S17S5S4S16A1M0G0A2M1S3S57Vm;A1G1S17S3S3S1S1dS3A1M2L_;M3S4dS11G0G0R1A3S6S16Vm;A2M4A2S5dVh;S9S16A1M5A2G0G2Lx;M6S12G0G0R1A3S16G6S11G0G0R2A3S16S17S3S3S93R2S6S16R1A2A2S3S17S3S3S94R2S6S16R3A2A2S3S17G0S3S56Vh;A1G0G3S4dR1G4A2S5dVh;S6S16R4A2A2S1aS3SfA2X1x2Lhd;A4L_;A4L_;A4Lnx;S3dS3S44Z5A1A2M7X4x2Lpr;G7X4x2X1x2S3S5eVm;G5G5A3L_;A4Ll;A4").

Definition dequeue_head (h : headloc) : M (option sptr) := ltac2:(tb__ "0|1|
S17S4S16A1M0G0S56Vh;A1G0G0S1dG0A1Lhd;R1S16S17S3G0S86Vh;R1A2S3S1aG0S6S16R2A2A2L_;A4Lm;S1aG0S9S16A1A2X4x2Lhd;A4").

Definition free_meta (m : sptr) : M unit := ltac2:(tb__ "0|1|
S17S3S3S76Vm;S81S9S16A1M0G0A2A2S3S8eS7dVm;A2L_;A4").

Definition usage_of (s : astate) (sc : Z) : Z := ltac2:(tb__ "0|0|
S3bVsc;S28Vs;A1A2").
Definition set_usage_of (sc : Z) (v : Z) : M unit := ltac2:(tb__ "0|0|
S35S18Sd5S6fVsc;Vv;S28R1A1A3R1A2Ls;A1").

Definition bounce_idx (sc : Z) : option Z := ltac2:(tb__ "0|1|
S1S4S0A1L_;S7SebZ7M0Vsc;A2SeaVsc;Z27A2A2S6S0Se9Vsc;G0A2A2S9S0A1X1x2").

Definition step_seq : M unit := ltac2:(tb__ "0|2|
S35S18S1S18L_;Se7S24R1A1M0ZffA2S96Z1M1S97Sf7S0Z0U20A3R1A2A2S96Se6G0G1A2R1A2X1x2Ls;A1").

Definition record_seq (sc : Z) : M unit := ltac2:(tb__ "0|0|
S4S0A1S1dS3A1Lx;S62Vsc;A1S0S35S18S97S6fR2S24R1A1S27R1A1A3R1A2Ls;A1Lk;S1aS3SfA2X4x2").

Definition account_bounce (sc : Z) : M unit := ltac2:(tb__ "0|1|
S4S0A1S1dS3A1Lx;S62Vsc;A1S0S35S18S3bR2S27R1A1A2S0S3bR3S1fR2A1A2S0S1S18L_;S7SdSe7R2Z0A2A1SeaSe9S24R3A1R2A2ZaA2A2S91S6fR4S1S0L_;SeaSe6R1Z1A2M0Z64A2G0Z96X1x2S1fR3A1A3R3A2R3X1x2Tb;Tuseq;Ls;A1Lk;S1aS3SfA2X4x2").

Definition decay_bounces (sc : Z) : M unit := ltac2:(tb__ "0|0|
S4S0A1S1dS3A1Lx;S62Vsc;A1S0S35S18S3bR2S1fR1A1A2S0S1S18L_;Se7R1Z0A2R2S91S6fR3Se9R1Z1A2S1fR2A1A3R2A2X1x2Tb;Ls;A1Lk;S1aS3SfA2X4x2").

Definition is_bouncing (s : astate) (sc : Z) : bool := ltac2:(tb__ "0|0|
S4S0A1S1Lx;S62Vsc;A1S0SebZ64S3bR1S1fVs;A1A2A2Lk;SeX4x2").

Definition new_region (k : rkind) (len : Z) : M nat := ltac2:(tb__ "0|0|
S17S18ScS36S18S15S3eS23R1A1A2ScS17S3ScS74S95S10S3eS23R2A1S2S3eS51Vk;Vlen;S8S0A1SbA4S8S3eA1A3A3R2A2A1S3S1aScR2A2L_;A4Tr;Ls;A4").
Definition upd_region (r : nat) (f : region -> region) : M unit := ltac2:(tb__ "0|1|
S35S18S95S72S3eS23R1A1M0Vr;Vf;Sf6S3eVr;G0S51S60Z0S8S0A1SeA4A4A1A4R1A2Ls;A1").

Definition area_from_brk : M bool := ltac2:(tb__ "0|8|
S17S18S1S36S18S1S1dS1A1M0L_;S7Se7S22R1A1Z0A2S63S1Lx;S2eR1A1M1SbSeScS0SbLpages;Lr;X63x3A2S63G0Lx;G1S17S1S1S48S9eA1S1S17S1S1S48S7fZ2M2A1A1S1S1G0Lok;M3R1S17ScS1S73S84Se8G2S37A2A2ScS17S3S1S35S18S6aZ1M4S6bS4fR2S37A2S75S7aR2G2A2R1A2A2A2Ls;A1S3S17S1S1S48S9fA1S1S1aS1SeA2M5L_;A4L_;A4Lr;A4S17S3S1S35S75S9bA1A1S3S1aS1SbA2M6L_;A4M7X1x2Lok;A4L_;A4G6ScS0S17S1S1S48S7fG4A1A1S1G3R1S17S3S1S6eR3S3eS51S84Se6S69R1A1S37A2S8S0A1SbA4Lrg;A2S3S17S3S1S35S18S6aG4S6bS4fR5Se8S37R4A2A2S75S7aR5Se6R4G4A2A2R1A2A2A2Ls;A1S3G5L_;A4L_;A4G7X1x2Lok;A4Lpages;Lr;X63x3G6X1x2Ls;A4").

Definition area_from_mmap : M bool := ltac2:(tb__ "0|4|
S17S18S1S36S18S1S1dS1A1M0L_;Se7S22R1A1Z0A2Sf5Z2S30R1A1M1A2S0S17S1S1S48Sa1Se8R1S37A2A1A1S1S1G0Lok;R1S17ScS1S73Sa8Se8R2S37A2A2ScS17S3S1S35S18Sd3Se6G1Z1M2A2S6aSe9R4G2A2S6bS4fR2S37A2R1A2A2A2Ls;A1S3S1aS1SbA2M3L_;A4Lr;A4S1aS1SeA2X1x2Lok;A4Tn;G3X1x2Ls;A4").

Definition open_area (need_unprotect : bool) : M bool := ltac2:(tb__ "0|4|
S17S18S1S36S18S2dR1A1S16S17S1S1S1S1dS1A1M0Lneed_unprotect;Vneed_unprotect;S48Sa3R1A1A1S1aS1SbA2M1X1x2S1S1G0L_;SdR1A1S1aS1SeA2S17S3S1S1S1dS3A1Lneed_unprotect;Vneed_unprotect;S6eSc6R2A1S3eS51Sc8R1A1S69R1A1S10S0ScaR1A1S2S0S8dR3A1S8S0A1A3A3Sc9R1A1A4Lrg;A2S1aS3SfA2X1x2S3S17S3S1S35S18S6aSe9S22R1A1Z1A2S6bS53R4Z1000A2ScfS6S16R4A2M2SceS4S16A1M3G3Lx;S2aR1A1S16S6S16R1A2Ls0;G2X4x2Sd0S10S16S2bR1A1S2S16R4S8S16A1A3A3S90Sa4S8fS53R4S9aA2R1A2A2A2A2A2A2A2Ls;A1S3G1L_;A4L_;A4X1x2Lprot_ok;A4Tp;Ls;A4").

Definition alloc_meta : M (option sptr) := ltac2:(tb__ "0|3|
S17S3S4S16A1M0S35Sd2SbA1A1S3S17G0G0Sb7S7dA1G0G0S1dG0A1M1Lfm;R1S16S1aG0S6S16R1A2A2Lm;S17S18G0S36S18S17S1G0S1S1dS1A1M2L_;SeaZ0S26R1A1A2S1aS1SbA2S17S1S1SafS1S17S1S1Sb0S1S1G2Lrs;R1Sc5R2A1S1aS1SeA2X1x2Lrs;A4Lnu;A4X1x2S1S1G1L_;SdR1A1S1aG0S9S16A1A2S17S18G0S36S18S2cR1A1S16S17S3G0S74S8fS53R1Sa5A2S90Se9S26R2A1Z1A2R2A2A2A1S3S17S3G0S76R2Sa7A2S3S1aG0S6S16R3A2A2L_;A4L_;A4Tm;Ls;A4X1x2Lok;A4Ls;A4X4x2Lfm;A4L_;A4").

Definition stride_of (am : ameta) : Z := ltac2:(tb__ "0|2|
S1S0L_;S7Se7S38Vam;A1Z0M0A2SdSe7S46Vam;A1M1G0A2A1A2Se9Se8G1Z1000A2S34A2S55S3cVam;A1A1X1x2").

Definition nth_slot (am : ameta) (i : Z) : slotst := ltac2:(tb__ "0|0|
Sf6S40SedVi;A1S4bVam;A1Sd9A4").
Definition upd_slot (am : ameta) (i : Z) (x : slotst) : ameta := ltac2:(tb__ "0|0|
SaeS72S40S4bVam;A1SedVi;A1Vx;A4Vam;A2").

Definition slot_start (am : ameta) (i : Z) : sptr := ltac2:(tb__ "0|0|
S53S4aVam;A1Se6S34Se8S6dVam;A1Vi;A2A2A2").

Definition slot_user (am : ameta) (i : Z) : option sptr := ltac2:(tb__ "0|0|
S4S3aA1S4S16A1Lx;S6cS5cVam;Vi;A2A1S3aS6S16S53S98Vam;Vi;A2Se8S34S65R1A1A2A2A2Lfr;S9S16A1X4x2").

Definition activate_group (m : sptr) : M Z := ltac2:(tb__ "0|0|
S17S1bS0S43Vm;A1S1bS17S3S0S58Se7S39R1A1Z0A2Z2A2S3S52S45R2A1A1S0S42R3A1S0S17S3S0S3fVm;S61SecR1R2A2S85Sf4R1R2A2R4A2A2A2S3S1aS0SecR2R3A2A2L_;A4Tmask;Tact;L_;A4Lam;A4").

Fixpoint span_loop (fuel : nat) (cnt span size : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if Z.lxor span (span + size - 1) <? 4096
           then span_loop f (cnt + 1) (span + size) size
           else cnt
  end.

Definition try_avail (sc : Z) : M Z := ltac2:(tb__ "0|12|
S17S4S16A1M0S0S56S70Vsc;A1M1A1M2G0G0S1dS0A1M3Lhd;R1S16S17S1bS0S43R1A1M4S1bS1G3L_;SdSe7S39R1A1M5Z0M6A2A1S71G5A1S0S17S3S0S3fR3S61Se9S39R2A1R1A2R2A2A2S3S1aS0R2A2L_;A4Tfirst;S17G0S0S1S1dG0A1L_;Se7S42R1A1M7G6A2S17S3G0S86G1R2A2S3G2L_;A4S17S3G0S5dG1S47R1A1M8A2S3S1aG0S47R2A1M9A2L_;A4X1x2G0G0G3Lom1;R1S16S17S1bS0G4S1bS17S16S0S1S1dS16A1MaL_;MbSe7G7S52S38R1A1A1A2G0GaLx;McG8S16S17S3S16S5dG1S6S16R1A2A2S3S1aS16R2A2MdL_;A4Lnx;MeS3dS16S44Z6A1A2X4x2GdX1x2S16S17S1bS0G4S1bG7S0S17S16S0GbSe7SecR1S52S45R2A1A1A2G6A2GbSdS4dG9S6S16R3A2A2A1GcG9GeS3dS16S44Z7A1A2X4x2S55S3cR2A1A1S0Se6S45R3A1Z2A2S0SddU12cR1Se6S34Se8R2R1A2A2R2A4S0S1S0L_;SeaSe6S38R5A1Z1MfA2M10R1A2G10R1X1x2S0S17S3S16S3fR7SacSe9R1GfA2R6A2A2S3S1aS16R8A2L_;A4Tcnt;Tcnt1;Tcnt0;Tsize;X1x2S1aS16R3A2X1x2S16S17S0S0Sa9R1A1S0S17S3S0S58SdSe7R1G6A2A1Z3A2S3S17S1bS0S43R3A1S1bS17S3S0Sb6S3cR1A1A1S3S71R4A1S0S17S1bS0S43R6A1S1bS17S3S0S3fR7S61Se9R6R2A2R1A2A2S3S1aS0R3A2L_;A4Lam3;A4Tfirst;L_;A4Lam3;A4L_;A4Lmask;A4Lm3;A4Tmask;Lam2;A4Lm2;A4Lam1;A4Lm1;S1aS0G6A2M11X4x2Lom1;A4X1x2Lam0;A4Lm0;G11X4x2Lhd;A4").

Definition enframe (g : sptr) (idx n ctr : Z) (k : fkind) : M sptr := ltac2:(tb__ "0|9|
S17S1bS16S43Vg;A1S1bS17S3S16Sc1S7SebZ0M0Vidx;A2SebVidx;S38R1A1A2A2ZcA2S3S6dR2A1S0SeeSe9Se9R1S4eA2Vn;A2S34A2S0S5cR4Vidx;A2S40S17S0S16S1S1dS0A1M1L_;Se7R2G0A2M2S1aS0G0A2S4S5S0S0A2M3A1G1Lx;S78R1A1G3G3G1Lp;R1S0S0S1aS0SecS1S0L_;M4G2Vctr;Se6R1Z1M5A2X1x2ZffM6A2A2Lh16;Lh3;X5x1Lp;S17S0S0Sb1Sa0SecVctr;G6A2A1A1S0S1aS0Sf2R1Z100A2A2Lz;A4X4x2X1x2S0G4SeaR3R1A2SefR3Sf0R3G5A2A2S0SefR1Sf0R1Z2A2A2S0SefR1Sf0R1Z4M7A2A2S0SecR4R1A2S0G4SeaR7R1A2Se9R1Se6R7G5A2A2R1X1x2Toff1;Tm3;Tm2;Tm1;R1X1x2S0S17S3S16S58SebR1R4A2G7A2S3Se9Se9Se9R6S4eA2Se8S34R2A2A2Vn;A2S0G4SebZ5M8R1A2G8R1X1x2S0S1G3L_;Se7R4G0A2SaS0S0S64S0Lk;Vk;Se6Vidx;Se8R1Z20A2A2Se6Vidx;Zc0A2X64x2SeeSe8R8Vidx;A2S34A2A4SaS0S0Ze0R4A4X1x2G3S17S3S16S3fVg;S79RbVidx;S5aS6G3R1A2S6S3aSc3R5Vn;Vk;A3A2A2A3A2S3S1aS16S53S98RcVidx;A2Se8S34R6A2A2A2L_;A4Thdr;Trsv;Treserved;L_;A4Toff;Loff0;A4Tsl;Tslack;Tstride;L_;A4Lam;A4").

Definition small_cnt (sc usage : Z) : Z := ltac2:(tb__ "0|5|
Sf6S13S0A1M0SedVsc;A1SdcS8S0A1A4G0S1S0L_;M1SdSeaVusage;Se8Z4M2S3bZ0R1A2M3A2A2A1G3G1SdSeaVusage;Se8G2S3bZ1R1A2M4A2A2A1G4S3bZ2R1A2X1x2X1x2Trow;").

Fixpoint halve_while_even (fuel : nat) (cnt usage : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if (Z.even cnt) && (usage <? 4 * cnt) then halve_while_even f (cnt / 2) usage else cnt
  end.

Fixpoint halve_while_big (fuel : nat) (cnt size : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if 65536 * UNIT <=? size * cnt then halve_while_big f (cnt / 2) size else cnt
  end.

Definition initial_cnt (sc usage : Z) : Z := ltac2:(tb__ "0|3|
S55Vsc;A1S0S1S0L_;M0SeaVsc;Z9A2SdbVsc;Vusage;A2SbcU8M1SbdG1S3bSecVsc;Z3A2Sc2A2Vusage;A3R1A3X1x2S0G0S7Se7R1Z1A2SebSe6Se8R2R1A2S34A2SeeS37Z2M2A2A2A2G2R1X1x2Tcnt;Tsize;").

Definition mmap_plan (s : astate) (sc req cnt0 usage0 : Z) : Z * Z := ltac2:(tb__ "0|b|
S55Vsc;A1S0S8aVs;Vsc;A2S1S1S0L_;M0S7Sf1Vsc;A1SeaVsc;Z20A2A2Se6Vusage0;S5fVs;Se6Vsc;Z1M1A2A2A2Vusage0;X1x2S0G0S7SeaR1Se8Z4M2Vcnt0;A2A2SdR2A1A2G0S7Se7SecVsc;Z3M3A2M4G1A2SeaSe8Z8S37A2Se8R3Vcnt0;A2M5A2M6A2Z2M7G0S7Se7G4G7A2SeaSe8G2S37A2M8G5A2A2G3G0S7Se7G4Z0A2M9G6A2G3G0S7G9SeaSe8G7S37A2G5A2A2Z5Vcnt0;X1x2X1x2X1x2X1x2Vcnt0;X1x2S0S68Se6Se8R4R1A2S34A2A1S0S1S5S0S0A2L_;MaS7SdR4A1SebR2Z7A2A2S68Se6Se6Vreq;S4eA2S34A2A1S0GaS14SeaR1Se6R6S34A2A2S7SebG8R1A2SeaR4Se8G7R3A2A2A2A2SaS0S0G1R1A4SaS0S0R3R2A4X1x2Trq;SaS0S0R2R1A4X1x2Tneeded;Tcnt;Tusage;Tnosmall;Tsize;").

Definition install_group (m : sptr) (sc cnt aidx maplen : Z) (mem : sptr) (sl : slotst) : M unit := ltac2:(tb__ "0|3|
S17S18S3S36S18S17S3S3Sd6Vsc;Se6S5fR1Vsc;A2Vcnt;A2A2S3S52Vaidx;A1S0Se9S52Se9Vcnt;Z1M0A2M1A1R1A2S0S17S3S3S3fVm;S49S9S16A1M2G2Vmem;Se9R2G0A2R1G1Vsc;Vmaplen;Vaidx;Sf7S40Vsl;SedVcnt;A1A3AaA2S3S8eS70Vsc;A1Vm;A2L_;A4Tfreed;Tavail;L_;A4Ls;A4").

Fixpoint alloc_slot (fuel : nat) (sc req : Z) : M Z :=
  match fuel with
  | O => fail FFuel
  | S fuel' =>
    first <- try_avail sc ;;
    if negb (first =? 0) then ret (ctz32 first)
    else
      og <- alloc_group fuel' sc req ;;
      match og with
      | None => ret (-1)
      | Some g => ret 0
      end
  end

with alloc_group (fuel : nat) (sc req : Z) : M (option sptr) :=
  match fuel with
  | O => fail FFuel
  | S fuel' =>
    om <- alloc_meta ;;
    match om with
    | None => ret None
    | Some m =>
      s <- get ;;
      let size := class_size sc in
      let usage := usage_of s sc in
      let cnt0 := initial_cnt sc usage in
      if PGSZ / 2 <? size * cnt0 + UNIT then

        let plan := mmap_plan s sc req cnt0 usage in
        account_bounce sc ;;
        step_seq ;;
        ok <- ask (KMmapRW (snd plan)) ;;
        if negb ok then free_meta m ;; ret None
        else

          r <- new_region RkMap (page_round (snd plan)) ;;
          s <- get ;;
          put (set_mmap_counter (Z.land (st_mmap_counter s + 1) (2^32 - 1)) s) ;;
          let cnt := fst plan in
          let a0 := (4096 - UNIT) / size - 1 in
          let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
          let aidx := if a1 <? 0 then 0 else a1 in
          install_group m sc cnt aidx (snd plan / 4096) (SP r 0) slot_zero ;;
          ret (Some m)
      else

        let total := UNIT + cnt0 * size - IB in
        let j := size_to_class total in
        idx <- alloc_slot fuel' j total ;;
        if idx <? 0 then free_meta m ;; ret None
        else
          hj <- get_head (HActive j) ;;
          match hj with
          | None => fail (FModel 8)
          | Some g =>

              amg <- getm g ;;
              mcheck (stride_of amg =? class_size j) 11 ;;
              s <- get ;;
              p <- enframe g idx (class_size j - IB) (st_mmap_counter s) FGroup ;;

              install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
              ret (Some m)
          end
    end
  end.

Definition NEST_FUEL : nat := 64%nat.

Definition malloc (n : Z) : M (option sptr) := ltac2:(tb__ "0|14|
S1S1dS4S16A1M0A1M1L_;M2Sd7Vn;A1S1aG0S9S16A1M3A2M4G2SebSa6Vn;A2Se6Se6Vn;S4eA2S34A2S0S17S1G0S48Sa2R1A1A1S1G2SdR1A1G4S17ScG0S73S60S68R2A1A2ScS17S3G0Se3S3S17G0G0SaaG0G0G1Log;R1S16S17S3G0S3fR1S49G3G3S4fR4Z0M5A2G5G5G5Z3fSeeS68R6A1Z1000A2G5S2S40SdaS8S40A1A3AaA2S3S17S18G0S36S18SecSe6S31R1A1M6Z1M7A2Se9Sf3Z2Z20M8A2G7A2A2S0S17S3G0S74Sd4R1R2A2A1S3S17S16G0S87R5G5Vn;R2S7cA5S16S1aG0S6S16R1A2A2Lp;M9A4L_;A4Tctr;Ls;A4L_;A4Lg;S17S1G0S48S80R3R5A2A1S1S17S3G0S6eR4S3eS51S60S69R1A1S8S0A1SeA4Lrg;A2S3G4L_;A4L_;A4X4x2Log;A4L_;A4Lr;A4X1x2Lok;A4Tneeded;S17S18G0S36S18Sd8Vn;A1S0Sf6G0SedR1A1MaS21R2A1G3A4G0S1S0L_;MbS7S7S7S7S7S4dR1G3A2SebZ4R2A2A2SeaR2G8A2A2SdSe7R2Z6A2A1A2Sf1R2A1A2Se7S5fR3R2A2G5A2A2S5fR3Se6R2G7A2A2S0G0S1Lx;Sf6G0SedSe6R3G7A2A1S21R4A1McG3A4S16S4S20A1S1Lx;S5bS1eR5A1R1A2S20S20S1Lm;R1G0G0SbLnext;Lprev;SbS1bS7Se7S39R1A1MdG5A2MeSe7S42R1A1G5A2A2Lam;X20x3Lm;SbX4x2Lh;SbX4x2S1S1S0Lhead_full;R1Se6R2Z3A2R2X1x2S0GbSebR1ZcA2Se6R5G7A2R5X1x2Tu;Thead_full;Tu;R2X1x2S0Sf6G0GaGcG3A4G0S17S4S5S16S0A2MfA1M10G0G0S1dG10A1M11Lg;R1S16S17S1bG10S43R1A1S1bS1G11L_;M12GeS1aG10S9GfA1A2M13S71GdA1S0S17S3G10S3fR3S61Se9S39R2A1R1A2R2A2A2S3S1aG10S6GfSaS16S0R4Sb5R2A1A4A2A2L_;A4Tfirst;X1x2Lam;A4Lgm;G13X4x2G10S17G10G0G10G11Lr;R1GfS1aG10S6GfR1A2A2Lgi;S17S0G10SabS83R3Vn;A3S0G12SeaR1G5A2G13S17G0G10S56S70R4A1A1G0G0G11Lhd;R1S16S1aG10S6GfSaS16S0R1R3A4A2A2Lgm;S3dG10S44Z9A1A2X4x2Lhd;A4X1x2Lidx;A4X4x2G10G10G1Lgi;R1GfGfG1Lp;R1S16S0S17S18G0S36S18S17S16G0S87R3R2Vn;G6S7cA5G9A4Ls;A4Lidx;Lgm;X5x1Lp;G4X4x2Lgi;A4Lr;A4Tg;Tsc;Tg0;Tsc0;Ls;A4X1x2X1x2").

Fixpoint find_in_slots (sl : list slotst) (base : sptr) (stride : Z) (i : Z) (p : sptr)
  : option Z :=
  match sl with
  | [] => None
  | x :: t =>
      match ss_fr x with
      | Some fr => if sptr_eqb (padd base (stride * i + UNIT * fr_off fr)) p then Some i
                   else find_in_slots t base stride (i + 1) p
      | None => find_in_slots t base stride (i + 1) p
      end
  end.

Fixpoint find_frame_in (l : list (sptr * mslot)) (p : sptr) : option (sptr * Z) :=
  match l with
  | [] => None
  | (m, MUsed am) :: t =>
      match find_in_slots (am_slots am) (padd (am_mem am) UNIT) (stride_of am) 0 p with
      | Some i => Some (m, i)
      | None => find_frame_in t p
      end
  | _ :: t => find_frame_in t p
  end.

Definition find_frame (p : sptr) : M (sptr * Z) := ltac2:(tb__ "0|1|
S17S18S5S16S0A2M0S36S18S4G0A1S1dG0A1Lx;S88S1eR1A1Vp;A2G0S1aG0R1A2Lx;S3dG0S7bZ0A1A2X4x2Ls;A4").

Definition okay_to_free (s : astate) (g : sptr) (am : ameta) : bool := ltac2:(tb__ "0|1|
S3cVam;A1S0S1S1L_;M0S14SebZ30R1A2SeaS6dVam;A1S55R1A1A2A2SbG0Se7S46Vam;A1Z0A2SbG0SdS4dS47Vam;A1S6S16Vg;A2A2A1SbG0SdS8aVs;R1A2A1SbSe6S38Vam;A1Z1A2S0S7SebSe8Z9R1A2S5fVs;R2A2A2SeaR1Z14A2A2Tcnt;X1x2X1x2X1x2X1x2Tsc;").

Definition forget_frame (g : sptr) (i : Z) : M unit := ltac2:(tb__ "0|0|
S17S1bS3S43Vg;A1S1bS5cR1Vi;A2S40S3fVg;S79R2Vi;S5aS78R1A1S9S3aA1A2A3A2Tsl;Lam;A4").

Definition slot_is_group (sl : slotst) : bool := ltac2:(tb__ "0|0|
S4S3aA1S1Lx;S6cVsl;A1S3aS64S1Lx;Sb9R1A1SeSbX64x2Lfr;SeX4x2").

Fixpoint nontrivial_free (fuel : nat) (g : sptr) (i : Z) : M (option (nat * Z)) :=
  match fuel with
  | O => fail FFuel
  | S fuel' =>
    am <- getm g ;;
    s <- get ;;
    let self := bit i in
    let sc := am_sc am in
    let mask := Z.lor (am_freed am) (am_avail am) in
    if (mask + self =? ones (am_last am)) && okay_to_free s g am then
      (match am_next am with
       | Some _ =>
           massert (sc <? 48) 5 ;;
           hd <- get_head (HActive sc) ;;
           let activate_new := osptr_eqb hd (Some g) in
           dequeue (HActive sc) g ;;
           hd' <- get_head (HActive sc) ;;
           match activate_new, hd' with
           | true, Some h => _ <- activate_group h ;; ret tt
           | _, _ => ret tt
           end
       | None => ret tt
       end) ;;

      am <- getm g ;;
      (if sc <? 48 then set_usage_of sc (usage_of s sc - (am_last am + 1)) else ret tt) ;;
      mi <- (if negb (am_maplen am =? 0) then
               step_seq ;; record_seq sc ;;
               ret (Some (prid (am_mem am), am_maplen am * 4096))
             else

               pf <- find_frame (am_mem am) ;;

               amp <- getm (fst pf) ;;
               mcheck (slot_is_group (nth_slot amp (snd pf))) 10 ;;
               forget_frame (fst pf) (snd pf) ;;
               nontrivial_free fuel' (fst pf) (snd pf)) ;;
      free_meta g ;;
      ret mi
    else
      (if mask =? 0 then
         massert (sc <? 48) 6 ;;
         hd <- get_head (HActive sc) ;;
         if osptr_eqb hd (Some g) then ret tt else queue (HActive sc) g
       else ret tt) ;;
      am <- getm g ;;
      setm g (am_set_freed (Z.lor (am_freed am) self) am) ;;
      ret None
  end.

Definition release_slot (g : sptr) (i : Z) : M unit := ltac2:(tb__ "0|2|
S17S1bS3S43Vg;A1S1bS5cR1Vi;A2S40S4S3aA1S40Lx;S6cR1A1S3aS1S40L_;Se7S65R1A1Z0M0A2S5aS6S5S0S0A2SaS0S0ZffG0A4A2S9S3aA1M1A2S5aS78R2A1G1A2X1x2Lfr;R1X4x2S40S3fVg;S79R3Vi;R1A3A2Tsl';Tsl;Lam;A4").

Definition free (p : option sptr) : M unit := ltac2:(tb__ "0|6|
S4S16A1S1dS3A1M0Lp;Vp;S16S17S5S16S0A2M1S3Sb8R1A1G1S12S16S0R1A3S16S11S16S0R2A3S0S17S1bS3S43R2A1S1bSb2R2A1S0S52S38R2A1A1S0S17S3S3Sc7R5R4A2S3S42R4A1S0SefR1S39R5A1A2S0S17S3S3S58Se7SecR1R5A2Z0M2A2Z7A2S3S1G0L_;S7SdSe7R3G2A2A1SdSe7Se6R2R6A2R5A2A1A2S17S1bS3S43R9A1S1bS3fRaS85Se6R4R7A2R1A2A2Lam;A4S17S4S5ScS0A2M3A1M4S3Sc4S83R9R8A3G4G4G0Lmi;R1G3G3G0Lp0;R1ScS0S17S1S3S48S80R2R1A2A1S1S6eR3S3eS51S60S69R1A1S8S0A1SeA4Lrg;A2L_;A4Llen;Lr;X5x1Lp0;S1aS3SfA2M5X4x2Lmi;A4X1x2L_;A4Tmask;Tfreed;L_;A4Tall;Tself;Lam;A4Ti;Tg;Lgi;A4Lp;G5X4x2").

Inductive outcome (A : Type) := ODone (a : A) | OFailed (f : failure) | OStarved.
Arguments ODone {A}. Arguments OFailed {A}. Arguments OStarved {A}.

Definition default_answer (q : kreq) : Z :=
  match q with KJunk pristine => pristine | _ => 1 end.

Fixpoint irun {S A} (fuel : nat) (t : itree S A) (ans : list (option Z)) (tr : list (kreq * Z))
  : outcome A * list (kreq * Z) * list (option Z) :=
  match fuel with
  | O => (OStarved, rev tr, ans)
  | S f =>
    match t with
    | IRet a => (ODone a, rev tr, ans)
    | IFail e => (OFailed e, rev tr, ans)
    | IAsk q _ k => let z := match hd None ans with Some z => z | None => default_answer q end in
                  irun f (k z) (tl ans) ((q, z) :: tr)
    end
  end.

Inductive op := Malloc (n : Z) | Free (k : nat)  .

Record srun := mkRun {
  sr_state : astate;
  sr_ptrs : list (option sptr);
  sr_trace : list (kreq * Z);
  sr_ans : list (option Z);
  sr_err : option failure
}.

Definition run_op (r : srun) (o : op) : srun := ltac2:(tb__ "0|14|
S4S4cA1S41Lx;Se0Vr;A1S4cVr;Lf;S19S41Lo;Vo;S0S5S5S67S5S4S16A1M0S18A2M1A1M2S13S5S8bS0A2M3A1M4A2M5S13S4S0A1A1M6A2S41Lx;S89S18G1U3e8M7Sc0R1Se2Vr;A1M8A2SdfVr;A1M9S8G3A1MaA6G5G6G5S41Lp0;R2G2G4G2S41Lo0;R2G1G1S41La;R1G0S18S59R1S10G0Se1Vr;A1MbS2G0R2S8G0A1A3A3S10G3S99Vr;A1McR4A3MdR6S9S4cA1MeA5Ls';Lp;X5x1La;S4cS59G8GbS10G3GcR2A3R4S6S4cR1A2A5Le;MfS59G8GbS10G3GcR1A3R3S6S4cS9dA2A5M10X67x3Ltr;Lo0;X5x1Lans;Lp0;X5x1Ln;ScS5S5S67S5S3S18A2M11A1M12G4A2M13G6A2S41Lx;S89S18G11G7SbbSf6G0R1GbS9S16A1A4G8A2G9GaA6G13G6G13S41Lp;R2G12G4G12S41Lo0;R2G11G11S41La;R1S3S18S59R1GbGdR6GeA5Ls';Lu;X5x1La;GfG10X67x3Ltr;Lo0;X5x1Lans;Lp;X5x1Lk;X19x2X4x2").

Definition run_script (ans : list (option Z)) (ops : list op) : srun := ltac2:(tb__ "0|0|
Sf9S41S19ScbVops;S59SbeS8S4S16A1A1S8S5S8bS0A2A1Vans;S9S4cA1A5A5").

Definition trace_of (ans : list (option Z)) (ops : list op) : list (kreq * Z) := ltac2:(tb__ "0|0|
S99SccVans;Vops;A2A1").

Definition refuse : option Z := Some 0.
Definition grant : option Z := None.

Example size_to_class_examples :
  map size_to_class [4096; 6048; 65632; 32864; 2262; 1120; 131051; 100; 24]
  = [28; 30; 44; 40; 24; 20; 47; 6; 1].
Proof. vm_compute. reflexivity. Qed.

Definition vec1_prefix : list op := ltac2:(tb__ "0|4|
S2S19S29Z1000A1S2S19S29Z17a0A1M0S2S19S29Z10060A1M1S2S19G1S2S19G1S2S19G1S2S19S1cU5A1S2S19S1cU4A1S2S19S1cU3A1S2S19S1cU2A1S2S19S1cU1A1S2S19G0S2S19S29Z8060A1M2S2S19G2S2S19S29Z20060A1M3S2S19G3S2S19S29Z8d6A1S2S19S1cUaA1S2S19S1cU9A1S2S19S1cU8A1S2S19S1cU7A1S2S19S1cU6A1S8S19A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Example vec1_trace :
  trace_of [] vec1_prefix =
  [(KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1);
   (KMmapRW 16384, 1); (KMmapRW 8192, 1);
   (KMmapRW 69632, 1); (KMmapRW 69632, 1); (KMmapRW 69632, 1); (KMmapRW 69632, 1);
   (KMunmap 6 69632, 1); (KMunmap 5 69632, 1); (KMunmap 4 69632, 1); (KMunmap 3 69632, 1);
   (KMunmap 2 8192, 1);
   (KMmapRW 8192, 1); (KMmapRW 36864, 1); (KMmapRW 36864, 1);
   (KMmapRW 131188, 1); (KMmapRW 131188, 1); (KMmapRW 8192, 1);
   (KMunmap 11 135168, 1); (KMunmap 10 135168, 1); (KMunmap 9 36864, 1);
   (KMunmap 8 36864, 1); (KMunmap 7 8192, 1)].
Proof. vm_compute. reflexivity. Qed.

Definition describe (s : astate) (p : option sptr) : option (Z * Z * Z * Z) := ltac2:(tb__ "0|9|
S4S16A1M0S4S5S5S5S0S0A2M1S0A2M2S0A2M3A1M4Lp;Vp;S16S4S5S16S0A2M5A1G4Lx;S88S1eVs;A1M6R1A2G5G5G4Lp0;R1S16S0S4S20A1G4Lx;S5bG6R2A2S20S20G4Lm0;R1G0G0S9G3A1M7Lnext;Lprev;G7S1bS4S3aA1G4Lx;S6cS5cR1R3A2A1S3aS6dR2A1S0Se9Se9Se9R1S4eA2Se8S34S65R2A1A2A2SbaR2A1A2S0S6G3SaG2S0SaG1S0SaS0S0R6Se6SeeSe8R2R6A2S34A2S65R3A1A2A4Sf2S8dR9A1Z1000A2A4S1S0L_;SebZ5M8R1A2G8R1X1x2A4A2Treserved;Tstride;Lfr;G7X4x2Lam;X20x3Lm0;G7X4x2Li;Lm;X5x1Lp0;G7X4x2Lp;G7X4x2").

Fixpoint run_descr (r : srun) (ops : list op) (acc : list (option (Z*Z*Z*Z)))
  : list (option (Z*Z*Z*Z)) :=
  match ops with
  | [] => rev acc
  | o :: t => let r' := run_op r o in
              match o with
              | Malloc _ => run_descr r' t (describe (sr_state r') (last (sr_ptrs r') None) :: acc)
              | Free _ => run_descr r' t acc
              end
  end.

Definition hdr_script : list op := ltac2:(tb__ "0|8|
S2S19S29Z1000A1S2S19S29Z17a0A1M0S2S19S29Z10060A1M1S2S19G1S2S19G1S2S19G1S2S19S1cU5A1S2S19S1cU4A1S2S19S1cU3A1S2S19S1cU2A1S2S19S1cU1A1S2S19G0S2S19S29Z8060A1M2S2S19G2S2S19S29Z20060A1M3S2S19G3S2S19S29Z8d6A1S2S19S1cUaA1S2S19S1cU9A1S2S19S1cU8A1S2S19S1cU7A1S2S19S1cU6A1S2S19S29Z1c58A1S2S19S29Z21fcA1S2S19S29Z4060A1S2S19S1cUeA1S2S19S1cUcA1S2S19S1cUdA1S2S19S1cUbA1S2S19S29Z64A1M4S2S19G4S2S19G4S2S19S1cU13A1S2S19S1cU14A1S2S19G4S2S19G4S2S19S29Z18A1M5S2S19G5S2S19S1cU18A1S2S19G5S2S19S29Z1388A1M6S2S19S1cU1bA1S2S19G6S2S19S29Z30d40A1M7S2S19S1cU1dA1S2S19G7S8S19A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Example hdr_script_matches_musl :
  run_descr (mkRun init_state [] [] [] None) hdr_script [] =
  map Some
  [(0,1,32,5); (0,2,48,5); (0,3,64,5); (0,4,80,5); (0,5,96,5); (0,6,112,5);
   (0,7,128,5); (0,8,144,5); (0,9,160,5); (0,10,176,5); (0,11,192,5); (0,12,208,5);
   (0,13,224,5); (0,14,240,5); (0,15,256,5);
   (0,0,64,5); (1,7,176,5); (2,14,288,5); (3,21,400,5); (0,0,560,5);
   (0,0,1072,4); (1,2,1104,4); (2,4,1136,4); (1,356,1616,5); (2,696,2960,5);
   (0,17,288,5); (0,18,304,5)].
Proof. vm_compute. reflexivity. Qed.

Example brk_refused_trace :
  trace_of [grant; refuse] [Malloc 4096; Malloc 100; Free 0; Free 1] =
  [(KBrkQuery, 1); (KBrkGrow 2, 0); (KMmapNone 8192, 1);
   (KMprotect (SP 0 4096), 1); (KMmapRW 16384, 1); (KMmapRW 4096, 1);
   (KMunmap 1 16384, 1); (KMunmap 2 4096, 1)].
Proof. vm_compute. reflexivity. Qed.

Example group_mmap_refused :
  sr_ptrs (run_script [grant; grant; grant; refuse] [Malloc 4096; Malloc 4096]) = [None; Some (SP 1 32)]
  /\ trace_of [grant; grant; grant; refuse] [Malloc 4096; Malloc 4096] =
     [(KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1); (KMmapRW 16384, 0); (KMmapRW 16384, 1)].
Proof. vm_compute. split; reflexivity. Qed.

Example direct_map_meta_refused :
  trace_of [grant; grant; refuse; refuse] [Malloc 200000] =
  [(KMmapRW 200020, 1); (KBrkQuery, 1); (KBrkGrow 2, 0); (KMmapNone 8192, 0);
   (KMunmap 0 200020, 1)]
  /\ sr_ptrs (run_script [grant; grant; refuse; refuse] [Malloc 200000]) = [None].
Proof. vm_compute. split; reflexivity. Qed.
