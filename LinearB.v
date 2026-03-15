(******************************************************************************)
(*                                                                            *)
(*                      LINEAR B ADMINISTRATIVE RECORDS                       *)
(*                                                                            *)
(*     Formalizing the Linear B palace archives: tablets, personnel,          *)
(*     commodities, places, counts, and allocation records in                 *)
(*     Mycenaean administrative ontology.                                     *)
(*                                                                            *)
(*     "the prosaic and often trivial details" - Michael Ventris, 1952        *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 9, 2026                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)
From Stdlib Require Import List ZArith Lia Bool.
Import ListNotations.

Set Implicit Arguments.
Local Set Warnings "-abstract-large-number".

Lemma NoDup_snoc :
  forall (A : Type) (xs : list A) (x : A),
    NoDup xs ->
    ~ In x xs ->
    NoDup (xs ++ [x]).
Proof.
  intros A xs.
  induction xs as [|h t IH]; intros x Hnodup Hnotin.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - inversion Hnodup as [|? ? Hnotin_h Hnodup_t]; subst.
    simpl in Hnotin.
    constructor.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply Hnotin_h. exact Hin.
      * simpl in Hin. destruct Hin as [Hx | Hfalse].
        -- subst h. apply Hnotin. simpl. auto.
        -- contradiction.
    + apply IH.
      * exact Hnodup_t.
      * intro Hin.
        apply Hnotin. simpl. auto.
Qed.

Lemma Forall_snoc :
  forall (A : Type) (predicate : A -> Prop) (xs : list A) (x : A),
    Forall predicate xs ->
    predicate x ->
    Forall predicate (xs ++ [x]).
Proof.
  intros A predicate xs x Hforall Hx.
  induction Hforall; simpl.
  - constructor; [exact Hx | constructor].
  - constructor; [exact H | exact IHHforall].
Qed.

Lemma Forall2_snoc :
  forall (A B : Type) (relation : A -> B -> Prop)
         (xs : list A) (ys : list B) (x : A) (y : B),
    Forall2 relation xs ys ->
    relation x y ->
    Forall2 relation (xs ++ [x]) (ys ++ [y]).
Proof.
  intros A B relation xs ys x y Hrel Hxy.
  induction Hrel; simpl.
  - constructor; [exact Hxy | constructor].
  - constructor; [exact H | exact IHHrel].
Qed.

Record tablet_id := { tablet_serial : nat }.
Record scribe_id := { scribe_serial : nat }.
Record person_id := { person_serial : nat }.
Record seal_id := { seal_serial : nat }.
Record place_id := { place_serial : nat }.
Record collective_id := { collective_serial : nat }.

Scheme Equality for tablet_id.
Scheme Equality for scribe_id.
Scheme Equality for person_id.
Scheme Equality for seal_id.
Scheme Equality for place_id.
Scheme Equality for collective_id.

Inductive palace_centre :=
| Knossos
| Pylos
| Thebes
| Mycenae
| Tiryns
| Chania.

Scheme Equality for palace_centre.

Inductive tablet_series :=
| Series_Aa
| Series_Ab
| Series_Ad
| Series_An
| Series_Cn
| Series_Eb
| Series_Fn
| Series_Jn
| Series_Kn
| Series_Ma
| Series_Na
| Series_Od
| Series_Ta
| Series_Ua
| Series_Unclassified.

Scheme Equality for tablet_series.

Inductive commodity :=
| Barley
| Wheat
| Olive
| OliveOil
| Wine
| Honey
| Wool
| Bronze
| Gold
| Textiles
| Cloth
| GarmentGoods
| ArmourGoods
| Figs
| Flax
| Saffron
| Cheese
| Livestock
| EquidStock
| SheepStock
| GoatStock
| PigStock
| CattleStock
| DeerStock
| ChariotGoods
| ChariotFrameGoods
| WheelGoods
| SpearGoods
| ArrowGoods
| SwordGoods.

Scheme Equality for commodity.

Inductive personnel_role :=
| ScribeRole
| CollectorRole
| ShepherdRole
| SmithRole
| PriestessRole
| ChariotRole
| PorterRole
| TextileWorkerRole.

Scheme Equality for personnel_role.

Inductive record_genre :=
| AllocationRecord
| ReceiptRecord
| InventoryRecord
| ObligationRecord.

Scheme Equality for record_genre.

Inductive flow_direction :=
| Incoming
| Outgoing.

Scheme Equality for flow_direction.

Record quantity := {
  quantity_value : nat;
  quantity_positive : (0 < quantity_value)%nat
}.

Coercion quantity_value : quantity >-> nat.

Inductive vowel :=
| VowelA
| VowelE
| VowelI
| VowelO
| VowelU.

Scheme Equality for vowel.

Inductive onset :=
| OnsetD
| OnsetJ
| OnsetK
| OnsetM
| OnsetN
| OnsetP
| OnsetQ
| OnsetR
| OnsetS
| OnsetT
| OnsetW
| OnsetZ.

Scheme Equality for onset.

Inductive basic_syllabogram :=
| SignA
| SignE
| SignI
| SignO
| SignU
| SignDa
| SignDe
| SignDi
| SignDo
| SignDu
| SignJa
| SignJe
| SignJo
| SignJu
| SignKa
| SignKe
| SignKi
| SignKo
| SignKu
| SignMa
| SignMe
| SignMi
| SignMo
| SignMu
| SignNa
| SignNe
| SignNi
| SignNo
| SignNu
| SignPa
| SignPe
| SignPi
| SignPo
| SignPu
| SignQa
| SignQe
| SignQi
| SignQo
| SignRa
| SignRe
| SignRi
| SignRo
| SignRu
| SignSa
| SignSe
| SignSi
| SignSo
| SignSu
| SignTa
| SignTe
| SignTi
| SignTo
| SignTu
| SignWa
| SignWe
| SignWi
| SignWo
| SignZa
| SignZe
| SignZo.

Inductive supplementary_syllabogram :=
| SignA2
| SignA3
| SignAu
| SignDwe
| SignDwo
| SignNwa
| SignPu2
| SignPte
| SignRa2
| SignRa3
| SignRo2
| SignTa2
| SignTwe
| SignTwo.

Inductive syllabogram :=
| BasicSign : basic_syllabogram -> syllabogram
| SupplementarySign : supplementary_syllabogram -> syllabogram.

Definition all_basic_syllabograms : list basic_syllabogram :=
  [ SignA; SignE; SignI; SignO; SignU;
    SignDa; SignDe; SignDi; SignDo; SignDu;
    SignJa; SignJe; SignJo; SignJu;
    SignKa; SignKe; SignKi; SignKo; SignKu;
    SignMa; SignMe; SignMi; SignMo; SignMu;
    SignNa; SignNe; SignNi; SignNo; SignNu;
    SignPa; SignPe; SignPi; SignPo; SignPu;
    SignQa; SignQe; SignQi; SignQo;
    SignRa; SignRe; SignRi; SignRo; SignRu;
    SignSa; SignSe; SignSi; SignSo; SignSu;
    SignTa; SignTe; SignTi; SignTo; SignTu;
    SignWa; SignWe; SignWi; SignWo;
    SignZa; SignZe; SignZo ].

Definition all_supplementary_syllabograms : list supplementary_syllabogram :=
  [ SignA2; SignA3; SignAu; SignDwe; SignDwo; SignNwa; SignPu2; SignPte;
    SignRa2; SignRa3; SignRo2; SignTa2; SignTwe; SignTwo ].

Definition basic_syllabogram_value (sign : basic_syllabogram) :
  option onset * vowel :=
  match sign with
  | SignA => (None, VowelA)
  | SignE => (None, VowelE)
  | SignI => (None, VowelI)
  | SignO => (None, VowelO)
  | SignU => (None, VowelU)
  | SignDa => (Some OnsetD, VowelA)
  | SignDe => (Some OnsetD, VowelE)
  | SignDi => (Some OnsetD, VowelI)
  | SignDo => (Some OnsetD, VowelO)
  | SignDu => (Some OnsetD, VowelU)
  | SignJa => (Some OnsetJ, VowelA)
  | SignJe => (Some OnsetJ, VowelE)
  | SignJo => (Some OnsetJ, VowelO)
  | SignJu => (Some OnsetJ, VowelU)
  | SignKa => (Some OnsetK, VowelA)
  | SignKe => (Some OnsetK, VowelE)
  | SignKi => (Some OnsetK, VowelI)
  | SignKo => (Some OnsetK, VowelO)
  | SignKu => (Some OnsetK, VowelU)
  | SignMa => (Some OnsetM, VowelA)
  | SignMe => (Some OnsetM, VowelE)
  | SignMi => (Some OnsetM, VowelI)
  | SignMo => (Some OnsetM, VowelO)
  | SignMu => (Some OnsetM, VowelU)
  | SignNa => (Some OnsetN, VowelA)
  | SignNe => (Some OnsetN, VowelE)
  | SignNi => (Some OnsetN, VowelI)
  | SignNo => (Some OnsetN, VowelO)
  | SignNu => (Some OnsetN, VowelU)
  | SignPa => (Some OnsetP, VowelA)
  | SignPe => (Some OnsetP, VowelE)
  | SignPi => (Some OnsetP, VowelI)
  | SignPo => (Some OnsetP, VowelO)
  | SignPu => (Some OnsetP, VowelU)
  | SignQa => (Some OnsetQ, VowelA)
  | SignQe => (Some OnsetQ, VowelE)
  | SignQi => (Some OnsetQ, VowelI)
  | SignQo => (Some OnsetQ, VowelO)
  | SignRa => (Some OnsetR, VowelA)
  | SignRe => (Some OnsetR, VowelE)
  | SignRi => (Some OnsetR, VowelI)
  | SignRo => (Some OnsetR, VowelO)
  | SignRu => (Some OnsetR, VowelU)
  | SignSa => (Some OnsetS, VowelA)
  | SignSe => (Some OnsetS, VowelE)
  | SignSi => (Some OnsetS, VowelI)
  | SignSo => (Some OnsetS, VowelO)
  | SignSu => (Some OnsetS, VowelU)
  | SignTa => (Some OnsetT, VowelA)
  | SignTe => (Some OnsetT, VowelE)
  | SignTi => (Some OnsetT, VowelI)
  | SignTo => (Some OnsetT, VowelO)
  | SignTu => (Some OnsetT, VowelU)
  | SignWa => (Some OnsetW, VowelA)
  | SignWe => (Some OnsetW, VowelE)
  | SignWi => (Some OnsetW, VowelI)
  | SignWo => (Some OnsetW, VowelO)
  | SignZa => (Some OnsetZ, VowelA)
  | SignZe => (Some OnsetZ, VowelE)
  | SignZo => (Some OnsetZ, VowelO)
  end.

Definition option_onset_eqb (lhs rhs : option onset) : bool :=
  match lhs, rhs with
  | None, None => true
  | Some lhs_onset, Some rhs_onset =>
      if onset_eq_dec lhs_onset rhs_onset then true else false
  | _, _ => false
  end.

Definition count_basic_row (row : option onset) : nat :=
  length (filter (fun sign =>
                    option_onset_eqb (fst (basic_syllabogram_value sign)) row)
                 all_basic_syllabograms).

Example basic_syllabary_size :
  length all_basic_syllabograms = 60.
Proof.
  vm_compute. reflexivity.
Qed.

Example supplementary_syllabary_size :
  length all_supplementary_syllabograms = 14.
Proof.
  vm_compute. reflexivity.
Qed.

Example pure_vowel_row_size :
  count_basic_row None = 5.
Proof.
  vm_compute. reflexivity.
Qed.

Example j_row_size :
  count_basic_row (Some OnsetJ) = 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example q_row_size :
  count_basic_row (Some OnsetQ) = 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example z_row_size :
  count_basic_row (Some OnsetZ) = 3.
Proof.
  vm_compute. reflexivity.
Qed.

Inductive ideogram :=
| IdeogramMan
| IdeogramWoman
| IdeogramDeer
| IdeogramEquid
| IdeogramMare
| IdeogramStallion
| IdeogramEwe
| IdeogramRam
| IdeogramSheGoat
| IdeogramHeGoat
| IdeogramSow
| IdeogramBoar
| IdeogramCow
| IdeogramBull
| IdeogramWheat
| IdeogramBarley
| IdeogramOlive
| IdeogramSpice
| IdeogramCyperus
| IdeogramKapo
| IdeogramKanako
| IdeogramOil
| IdeogramWine
| IdeogramArepa
| IdeogramMeri
| IdeogramBronze
| IdeogramGold
| IdeogramWool
| IdeogramCloth
| IdeogramGarment
| IdeogramArmour
| IdeogramMonth
| IdeogramTree
| IdeogramHelmet
| IdeogramFootstool
| IdeogramBathtub
| IdeogramSpear
| IdeogramArrow
| IdeogramSword
| IdeogramWheeledChariot
| IdeogramChariot
| IdeogramChariotFrame
| IdeogramWheel.

Scheme Equality for ideogram.

Inductive aegean_number_sign :=
| NumberOne
| NumberTwo
| NumberThree
| NumberFour
| NumberFive
| NumberSix
| NumberSeven
| NumberEight
| NumberNine
| NumberTen
| NumberTwenty
| NumberThirty
| NumberForty
| NumberFifty
| NumberSixty
| NumberSeventy
| NumberEighty
| NumberNinety
| NumberOneHundred
| NumberTwoHundred
| NumberThreeHundred
| NumberFourHundred
| NumberFiveHundred
| NumberSixHundred
| NumberSevenHundred
| NumberEightHundred
| NumberNineHundred
| NumberOneThousand
| NumberTwoThousand
| NumberThreeThousand
| NumberFourThousand
| NumberFiveThousand
| NumberSixThousand
| NumberSevenThousand
| NumberEightThousand
| NumberNineThousand
| NumberTenThousand
| NumberTwentyThousand
| NumberThirtyThousand
| NumberFortyThousand
| NumberFiftyThousand
| NumberSixtyThousand
| NumberSeventyThousand
| NumberEightyThousand
| NumberNinetyThousand.

Scheme Equality for aegean_number_sign.

Definition aegean_number_value (sign : aegean_number_sign) : nat :=
  match sign with
  | NumberOne => 1
  | NumberTwo => 2
  | NumberThree => 3
  | NumberFour => 4
  | NumberFive => 5
  | NumberSix => 6
  | NumberSeven => 7
  | NumberEight => 8
  | NumberNine => 9
  | NumberTen => 10
  | NumberTwenty => 20
  | NumberThirty => 30
  | NumberForty => 40
  | NumberFifty => 50
  | NumberSixty => 60
  | NumberSeventy => 70
  | NumberEighty => 80
  | NumberNinety => 90
  | NumberOneHundred => 100
  | NumberTwoHundred => 200
  | NumberThreeHundred => 300
  | NumberFourHundred => 400
  | NumberFiveHundred => 500
  | NumberSixHundred => 600
  | NumberSevenHundred => 700
  | NumberEightHundred => 800
  | NumberNineHundred => 900
  | NumberOneThousand => 1000
  | NumberTwoThousand => 2000
  | NumberThreeThousand => 3000
  | NumberFourThousand => 4000
  | NumberFiveThousand => 5000
  | NumberSixThousand => 6000
  | NumberSevenThousand => 7000
  | NumberEightThousand => 8000
  | NumberNineThousand => 9000
  | NumberTenThousand => 10000
  | NumberTwentyThousand => 20000
  | NumberThirtyThousand => 30000
  | NumberFortyThousand => 40000
  | NumberFiftyThousand => 50000
  | NumberSixtyThousand => 60000
  | NumberSeventyThousand => 70000
  | NumberEightyThousand => 80000
  | NumberNinetyThousand => 90000
  end.

Definition aegean_numeral_value (signs : list aegean_number_sign) : nat :=
  fold_right Nat.add 0 (map aegean_number_value signs).

Example aegean_numeral_12 :
  aegean_numeral_value [NumberTen; NumberTwo] = 12.
Proof.
  vm_compute. reflexivity.
Qed.

Example aegean_numeral_708 :
  aegean_numeral_value [NumberSevenHundred; NumberEight] = 708.
Proof.
  vm_compute. reflexivity.
Qed.

Inductive aegean_measure_sign :=
| WeightBaseUnit
| WeightFirstSubunit
| WeightSecondSubunit
| WeightThirdSubunit
| WeightFourthSubunit
| DryMeasureFirstSubunit
| LiquidMeasureFirstSubunit
| MeasureSecondSubunit
| MeasureThirdSubunit.

Scheme Equality for aegean_measure_sign.

Inductive measure_domain :=
| WeightMeasure
| DryMeasure
| LiquidMeasure
| GenericMeasure.

Definition measure_sign_domain (sign : aegean_measure_sign) : measure_domain :=
  match sign with
  | WeightBaseUnit
  | WeightFirstSubunit
  | WeightSecondSubunit
  | WeightThirdSubunit
  | WeightFourthSubunit => WeightMeasure
  | DryMeasureFirstSubunit => DryMeasure
  | LiquidMeasureFirstSubunit => LiquidMeasure
  | MeasureSecondSubunit
  | MeasureThirdSubunit => GenericMeasure
  end.

Inductive word_separator :=
| SeparatorLine
| SeparatorDot
| CheckMark.

Inductive principal :=
| NamedWorker : person_id -> personnel_role -> principal
| AdministrativeOffice : place_id -> principal
| CollectiveLabor : collective_id -> principal.

Record line_item := {
  line_number : nat;
  line_subject : principal;
  line_target : place_id;
  line_genre : record_genre;
  line_direction : flow_direction;
  line_commodity : commodity;
  line_quantity : quantity;
  line_seals : list seal_id
}.

Record tablet := {
  tablet_identifier : tablet_id;
  tablet_series_of : tablet_series;
  tablet_scribe : scribe_id;
  tablet_archive_centre : palace_centre;
  tablet_findspot : place_id;
  tablet_lines : list line_item
}.

Record archive := {
  archive_centre : palace_centre;
  archive_tablets : list tablet
}.

Inductive archive_site :=
| SiteKnossos
| SitePylos
| SiteThebes
| SiteMycenae
| SiteTiryns
| SiteChania
| SiteMidea
| SiteOrchomenos
| SiteEleusis
| SiteSparta
| SiteDimini
| SiteIklaina
| SiteAyiosVasileios.

Inductive document_support :=
| SupportTablet
| SupportNodule
| SupportLabel
| SupportStirrupJar.

Inductive tablet_shape :=
| PageShaped
| LeafShaped.

Inductive administrative_domain :=
| MetalsDomain
| HerdDomain
| EquipmentDomain
| CerealDomain
| LiquidDomain
| TextileDomain
| SpiceDomain
| MixedDomain.

Definition commodity_domain (tracked : commodity) : administrative_domain :=
  match tracked with
  | Bronze
  | Gold => MetalsDomain
  | Livestock
  | EquidStock
  | SheepStock
  | GoatStock
  | PigStock
  | CattleStock
  | DeerStock => HerdDomain
  | ChariotGoods
  | ChariotFrameGoods
  | WheelGoods
  | SpearGoods
  | ArrowGoods
  | SwordGoods
  | ArmourGoods => EquipmentDomain
  | Barley
  | Wheat => CerealDomain
  | OliveOil
  | Wine
  | Honey => LiquidDomain
  | Wool
  | Textiles
  | Cloth
  | GarmentGoods
  | Flax => TextileDomain
  | Saffron => SpiceDomain
  | Olive
  | Figs
  | Cheese => MixedDomain
  end.

Definition series_domain (series : tablet_series) : administrative_domain :=
  match series with
  | Series_Cn => HerdDomain
  | Series_Jn => MetalsDomain
  | Series_Ta => EquipmentDomain
  | Series_Aa
  | Series_Ab
  | Series_Ad => TextileDomain
  | Series_Fn
  | Series_Kn => LiquidDomain
  | Series_Ma
  | Series_Na
  | Series_Od
  | Series_Ua
  | Series_Eb
  | Series_An
  | Series_Unclassified => MixedDomain
  end.

Definition series_allows_commodity
  (series : tablet_series) (tracked : commodity) : Prop :=
  match series with
  | Series_Cn =>
      match tracked with
      | Livestock
      | SheepStock
      | GoatStock
      | PigStock
      | CattleStock
      | DeerStock => True
      | _ => False
      end
  | Series_Jn =>
      match tracked with
      | Bronze
      | Gold => True
      | _ => False
      end
  | Series_Ta =>
      match tracked with
      | ChariotGoods
      | ChariotFrameGoods
      | WheelGoods
      | SpearGoods
      | ArrowGoods
      | SwordGoods
      | ArmourGoods => True
      | _ => False
      end
  | Series_Aa
  | Series_Ab
  | Series_Ad =>
      match tracked with
      | Wool
      | Textiles
      | Cloth
      | GarmentGoods
      | Flax => True
      | _ => False
      end
  | Series_Fn
  | Series_Kn =>
      match tracked with
      | OliveOil
      | Wine
      | Honey => True
      | _ => False
      end
  | Series_Eb =>
      match tracked with
      | Barley
      | Wheat => True
      | _ => False
      end
  | _ => True
  end.

Definition line_fits_series (series : tablet_series) (line : line_item) : Prop :=
  series_allows_commodity series (line_commodity line).

Definition tablet_series_compatible (tab : tablet) : Prop :=
  Forall (line_fits_series (tablet_series_of tab)) (tablet_lines tab).

Inductive scripted_token :=
| TokenSyllabogram : syllabogram -> scripted_token
| TokenIdeogram : ideogram -> scripted_token
| TokenNumber : aegean_number_sign -> scripted_token
| TokenMeasure : aegean_measure_sign -> scripted_token
| TokenSeparator : word_separator -> scripted_token.

Record inscribed_entry := {
  entry_tokens : list scripted_token;
  entry_ideogram : option ideogram;
  entry_numerals : list aegean_number_sign;
  entry_measure : option aegean_measure_sign
}.

Definition token_number_total (tokens : list scripted_token) : nat :=
  fold_right Nat.add 0
             (map (fun token =>
                     match token with
                     | TokenNumber number => aegean_number_value number
                     | _ => 0
                     end)
                  tokens).

Fixpoint token_has_ideogram (target : ideogram) (tokens : list scripted_token) : bool :=
  match tokens with
  | [] => false
  | TokenIdeogram actual :: rest =>
      if ideogram_eq_dec actual target then true else token_has_ideogram target rest
  | _ :: rest => token_has_ideogram target rest
  end.

Fixpoint token_has_measure (target : aegean_measure_sign) (tokens : list scripted_token) : bool :=
  match tokens with
  | [] => false
  | TokenMeasure actual :: rest =>
      if aegean_measure_sign_eq_dec actual target then true else token_has_measure target rest
  | _ :: rest => token_has_measure target rest
  end.

Fixpoint extract_number_tokens (tokens : list scripted_token) : list aegean_number_sign :=
  match tokens with
  | [] => []
  | TokenNumber number :: rest => number :: extract_number_tokens rest
  | _ :: rest => extract_number_tokens rest
  end.

Fixpoint extract_ideogram_tokens (tokens : list scripted_token) : list ideogram :=
  match tokens with
  | [] => []
  | TokenIdeogram ideogram :: rest => ideogram :: extract_ideogram_tokens rest
  | _ :: rest => extract_ideogram_tokens rest
  end.

Fixpoint extract_measure_tokens (tokens : list scripted_token) : list aegean_measure_sign :=
  match tokens with
  | [] => []
  | TokenMeasure measure :: rest => measure :: extract_measure_tokens rest
  | _ :: rest => extract_measure_tokens rest
  end.

Definition entry_tokens_realize_metadata (entry : inscribed_entry) : Prop :=
  token_number_total (entry_tokens entry) = aegean_numeral_value (entry_numerals entry) /\
  match entry_ideogram entry with
  | Some ideogram => token_has_ideogram ideogram (entry_tokens entry) = true
  | None => True
  end /\
  match entry_measure entry with
  | Some measure => token_has_measure measure (entry_tokens entry) = true
  | None => True
  end.

Definition entry_tokens_canonical (entry : inscribed_entry) : Prop :=
  extract_number_tokens (entry_tokens entry) = entry_numerals entry /\
  match entry_ideogram entry with
  | Some ideogram => extract_ideogram_tokens (entry_tokens entry) = [ideogram]
  | None => extract_ideogram_tokens (entry_tokens entry) = []
  end /\
  match entry_measure entry with
  | Some measure => extract_measure_tokens (entry_tokens entry) = [measure]
  | None => extract_measure_tokens (entry_tokens entry) = []
  end.

Definition commodity_ideogram (tracked : commodity) : option ideogram :=
  match tracked with
  | Barley => Some IdeogramBarley
  | Wheat => Some IdeogramWheat
  | Olive => Some IdeogramOlive
  | OliveOil => Some IdeogramOil
  | Wine => Some IdeogramWine
  | Wool => Some IdeogramWool
  | Bronze => Some IdeogramBronze
  | Gold => Some IdeogramGold
  | Textiles
  | Cloth => Some IdeogramCloth
  | GarmentGoods => Some IdeogramGarment
  | ArmourGoods => Some IdeogramArmour
  | Figs => None
  | Flax => None
  | Saffron => Some IdeogramSpice
  | Honey => None
  | Cheese => None
  | Livestock => None
  | EquidStock => Some IdeogramEquid
  | SheepStock => Some IdeogramEwe
  | GoatStock => Some IdeogramSheGoat
  | PigStock => Some IdeogramSow
  | CattleStock => Some IdeogramCow
  | DeerStock => Some IdeogramDeer
  | ChariotGoods => Some IdeogramChariot
  | ChariotFrameGoods => Some IdeogramChariotFrame
  | WheelGoods => Some IdeogramWheel
  | SpearGoods => Some IdeogramSpear
  | ArrowGoods => Some IdeogramArrow
  | SwordGoods => Some IdeogramSword
  end.

Definition commodity_measure_domain (tracked : commodity) : option measure_domain :=
  match tracked with
  | Bronze
  | Gold => Some WeightMeasure
  | Barley
  | Wheat
  | Olive => Some DryMeasure
  | OliveOil
  | Wine
  | Honey => Some LiquidMeasure
  | _ => None
  end.

Definition entry_measure_compatible (tracked : commodity)
  (measure : option aegean_measure_sign) : Prop :=
  match commodity_measure_domain tracked, measure with
  | Some expected, Some actual => measure_sign_domain actual = expected \/ measure_sign_domain actual = GenericMeasure
  | Some _, None => False
  | None, _ => True
  end.

Definition inscribed_entry_consistent (line : line_item) (entry : inscribed_entry) : Prop :=
  aegean_numeral_value (entry_numerals entry) = line_quantity line /\
  entry_ideogram entry = commodity_ideogram (line_commodity line) /\
  entry_measure_compatible (line_commodity line) (entry_measure entry).

Record documentary_tablet := {
  documentary_semantics : tablet;
  documentary_site : archive_site;
  documentary_support : document_support;
  documentary_shape : option tablet_shape;
  documentary_entries : list inscribed_entry
}.

Definition support_shape_consistent (doc : documentary_tablet) : Prop :=
  match documentary_support doc with
  | SupportTablet => exists shape, documentary_shape doc = Some shape
  | SupportNodule
  | SupportLabel
  | SupportStirrupJar => documentary_shape doc = None
  end.

Definition site_affiliated_centre (site : archive_site) : option palace_centre :=
  match site with
  | SiteKnossos => Some Knossos
  | SitePylos => Some Pylos
  | SiteThebes => Some Thebes
  | SiteMycenae => Some Mycenae
  | SiteTiryns => Some Tiryns
  | SiteChania => Some Chania
  | SiteMidea => Some Mycenae
  | SiteIklaina => Some Pylos
  | _ => None
  end.

Definition documentary_site_consistent (doc : documentary_tablet) : Prop :=
  match site_affiliated_centre (documentary_site doc) with
  | Some centre => tablet_archive_centre (documentary_semantics doc) = centre
  | None => True
  end.

Definition series_shape_compatible (doc : documentary_tablet) : Prop :=
  match tablet_series_of (documentary_semantics doc) with
  | Series_Jn
  | Series_Ta => documentary_shape doc = Some PageShaped
  | _ => True
  end.

Definition line_effect (tracked : commodity) (line : line_item) : Z :=
  if commodity_eq_dec tracked (line_commodity line)
  then
    match line_direction line with
    | Incoming => Z.of_nat (line_quantity line)
    | Outgoing => - Z.of_nat (line_quantity line)
    end
  else 0%Z.

Definition tablet_balance (tracked : commodity) (tab : tablet) : Z :=
  fold_right Z.add 0%Z (map (line_effect tracked) (tablet_lines tab)).

Definition archive_balance (tracked : commodity) (ar : archive) : Z :=
  fold_right Z.add 0%Z (map (tablet_balance tracked) (archive_tablets ar)).

Definition append_line (tab : tablet) (line : line_item) : tablet :=
  {|
    tablet_identifier := tablet_identifier tab;
    tablet_series_of := tablet_series_of tab;
    tablet_scribe := tablet_scribe tab;
    tablet_archive_centre := tablet_archive_centre tab;
    tablet_findspot := tablet_findspot tab;
    tablet_lines := tablet_lines tab ++ [line]
  |}.

Definition register_tablet (ar : archive) (tab : tablet) : archive :=
  {|
    archive_centre := archive_centre ar;
    archive_tablets := archive_tablets ar ++ [tab]
  |}.

Definition append_documentary_entry
  (doc : documentary_tablet) (line : line_item) (entry : inscribed_entry) :
  documentary_tablet :=
  {|
    documentary_semantics := append_line (documentary_semantics doc) line;
    documentary_site := documentary_site doc;
    documentary_support := documentary_support doc;
    documentary_shape := documentary_shape doc;
    documentary_entries := documentary_entries doc ++ [entry]
  |}.

Definition positive_line_number (line : line_item) : Prop :=
  (0 < line_number line)%nat.

Definition line_attested (line : line_item) : Prop :=
  line_direction line = Incoming \/ line_seals line <> [].

Definition tablet_well_formed (tab : tablet) : Prop :=
  NoDup (map line_number (tablet_lines tab)) /\
  Forall positive_line_number (tablet_lines tab) /\
  Forall line_attested (tablet_lines tab).

Definition tablet_registered_in (ar : archive) (tab : tablet) : Prop :=
  tablet_archive_centre tab = archive_centre ar.

Definition archive_well_formed (ar : archive) : Prop :=
  NoDup (map tablet_identifier (archive_tablets ar)) /\
  Forall (fun tab => tablet_registered_in ar tab /\ tablet_well_formed tab)
         (archive_tablets ar).

Definition documentary_tablet_well_formed (doc : documentary_tablet) : Prop :=
  tablet_well_formed (documentary_semantics doc) /\
  tablet_series_compatible (documentary_semantics doc) /\
  support_shape_consistent doc /\
  documentary_site_consistent doc /\
  series_shape_compatible doc /\
  Forall2 inscribed_entry_consistent
          (tablet_lines (documentary_semantics doc))
          (documentary_entries doc).

Definition documentary_tokens_sound (doc : documentary_tablet) : Prop :=
  Forall entry_tokens_realize_metadata (documentary_entries doc).

Definition documentary_tokens_canonical (doc : documentary_tablet) : Prop :=
  Forall entry_tokens_canonical (documentary_entries doc).

Record documentary_archive := {
  documentary_archive_semantics : archive;
  documentary_documents : list documentary_tablet
}.

Definition documentary_archive_well_formed (dar : documentary_archive) : Prop :=
  archive_well_formed (documentary_archive_semantics dar) /\
  Forall documentary_tablet_well_formed (documentary_documents dar) /\
  Forall documentary_tokens_sound (documentary_documents dar) /\
  map documentary_semantics (documentary_documents dar) =
  archive_tablets (documentary_archive_semantics dar).

Lemma line_attested_outgoing_has_seal :
  forall line,
    line_direction line = Outgoing ->
    line_attested line ->
    exists seal rest, line_seals line = seal :: rest.
Proof.
  intros line Hdir Hattested.
  unfold line_attested in Hattested.
  destruct Hattested as [Hincoming | Hsealed].
  - rewrite Hdir in Hincoming. discriminate.
  - destruct (line_seals line) as [|seal rest] eqn:Hseals.
    + exfalso. apply Hsealed. reflexivity.
    + exists seal, rest. reflexivity.
Qed.

Theorem append_line_preserves_tablet_well_formed :
  forall tab line,
    tablet_well_formed tab ->
    positive_line_number line ->
    line_attested line ->
    ~ In (line_number line) (map line_number (tablet_lines tab)) ->
    tablet_well_formed (append_line tab line).
Proof.
  intros tab line [Hnodup [Hpositive Hattested]] Hlinepos Hlineattested Hfresh.
  unfold tablet_well_formed.
  split.
  - unfold append_line. simpl.
    rewrite map_app. simpl.
    apply NoDup_snoc; assumption.
  - split.
    + unfold append_line. simpl.
      rewrite Forall_app. split.
      * exact Hpositive.
      * constructor; [exact Hlinepos | constructor].
    + unfold append_line. simpl.
      rewrite Forall_app. split.
      * exact Hattested.
      * constructor; [exact Hlineattested | constructor].
Qed.

Theorem append_line_preserves_tablet_series_compatible :
  forall tab line,
    tablet_series_compatible tab ->
    line_fits_series (tablet_series_of tab) line ->
    tablet_series_compatible (append_line tab line).
Proof.
  intros tab line Hcompatible Hfits.
  unfold tablet_series_compatible in *.
  unfold append_line. simpl.
  rewrite Forall_app.
  split.
  - exact Hcompatible.
  - constructor; [exact Hfits | constructor].
Qed.

Lemma inscribed_entry_consistent_positive :
  forall line entry,
    inscribed_entry_consistent line entry ->
    (0 < aegean_numeral_value (entry_numerals entry))%nat.
Proof.
  intros line entry [Hvalue _].
  rewrite Hvalue.
  exact (quantity_positive (line_quantity line)).
Qed.

Theorem append_documentary_entry_preserves_documentary_tablet_well_formed :
  forall doc line entry,
    documentary_tablet_well_formed doc ->
    positive_line_number line ->
    line_attested line ->
    ~ In (line_number line)
         (map line_number (tablet_lines (documentary_semantics doc))) ->
    line_fits_series (tablet_series_of (documentary_semantics doc)) line ->
    inscribed_entry_consistent line entry ->
    documentary_tablet_well_formed (append_documentary_entry doc line entry).
Proof.
  intros doc line entry
         [Htablet [Hseries [Hsupport [Hsite [Hshape Halign]]]]]
         Hlinepos Hlineattested Hfresh Hfits Hentry.
  unfold documentary_tablet_well_formed.
  split.
  - apply append_line_preserves_tablet_well_formed; assumption.
  - split.
    + apply append_line_preserves_tablet_series_compatible; assumption.
    + split.
      * unfold append_documentary_entry. simpl. exact Hsupport.
      * split.
        -- unfold append_documentary_entry. simpl. exact Hsite.
        -- split.
           ++ unfold append_documentary_entry. simpl. exact Hshape.
           ++ unfold append_documentary_entry. simpl.
              apply Forall2_snoc; assumption.
Qed.

Theorem append_documentary_entry_preserves_tokens_sound :
  forall doc line entry,
    documentary_tokens_sound doc ->
    entry_tokens_realize_metadata entry ->
    documentary_tokens_sound (append_documentary_entry doc line entry).
Proof.
  intros doc line entry Hsound Hentry.
  unfold documentary_tokens_sound in *.
  unfold append_documentary_entry. simpl.
  apply Forall_snoc; assumption.
Qed.

Theorem append_documentary_entry_preserves_tokens_canonical :
  forall doc line entry,
    documentary_tokens_canonical doc ->
    entry_tokens_canonical entry ->
    documentary_tokens_canonical (append_documentary_entry doc line entry).
Proof.
  intros doc line entry Hcanonical Hentry.
  unfold documentary_tokens_canonical in *.
  unfold append_documentary_entry. simpl.
  apply Forall_snoc; assumption.
Qed.

Lemma token_number_total_extract_number_tokens :
  forall tokens,
    token_number_total tokens = aegean_numeral_value (extract_number_tokens tokens).
Proof.
  induction tokens as [|token tokens IHtokens]; simpl.
  - reflexivity.
  - destruct token as [syllabogram | ideogram | number | measure | separator];
      simpl; try exact IHtokens.
    change
      (aegean_number_value number + token_number_total tokens =
       aegean_number_value number +
       aegean_numeral_value (extract_number_tokens tokens)).
    rewrite IHtokens.
    reflexivity.
Qed.

Lemma extract_ideogram_tokens_head_sound :
  forall tokens ideogram rest,
    extract_ideogram_tokens tokens = ideogram :: rest ->
    token_has_ideogram ideogram tokens = true.
Proof.
  induction tokens as [|token tokens IHtokens]; intros ideogram rest Hextract.
  - discriminate.
  - destruct token as [syllabogram | actual_ideogram | number | measure | separator];
      simpl in *.
    + eapply IHtokens. exact Hextract.
    + inversion Hextract; subst.
      destruct (ideogram_eq_dec ideogram ideogram).
      * reflexivity.
      * contradiction.
    + eapply IHtokens. exact Hextract.
    + eapply IHtokens. exact Hextract.
    + eapply IHtokens. exact Hextract.
Qed.

Lemma extract_measure_tokens_head_sound :
  forall tokens measure rest,
    extract_measure_tokens tokens = measure :: rest ->
    token_has_measure measure tokens = true.
Proof.
  induction tokens as [|token tokens IHtokens]; intros measure rest Hextract.
  - discriminate.
  - destruct token as [syllabogram | ideogram | number | actual_measure | separator];
      simpl in *.
    + eapply IHtokens. exact Hextract.
    + eapply IHtokens. exact Hextract.
    + eapply IHtokens. exact Hextract.
    + inversion Hextract; subst.
      destruct (aegean_measure_sign_eq_dec measure measure).
      * reflexivity.
      * contradiction.
    + eapply IHtokens. exact Hextract.
Qed.

Lemma entry_tokens_canonical_sound :
  forall entry,
    entry_tokens_canonical entry ->
    entry_tokens_realize_metadata entry.
Proof.
  intros entry [Hnumbers [Hideogram Hmeasure]].
  unfold entry_tokens_realize_metadata.
  split.
  - rewrite token_number_total_extract_number_tokens.
    rewrite Hnumbers.
    reflexivity.
  - split.
    + destruct (entry_ideogram entry) as [ideogram |] eqn:Hentry_ideogram.
      * change [ideogram] with (ideogram :: []) in Hideogram.
        eapply extract_ideogram_tokens_head_sound.
        exact Hideogram.
      * exact I.
    + destruct (entry_measure entry) as [measure |] eqn:Hentry_measure.
      * change [measure] with (measure :: []) in Hmeasure.
        eapply extract_measure_tokens_head_sound.
        exact Hmeasure.
      * exact I.
Qed.

Lemma documentary_tokens_canonical_sound :
  forall doc,
    documentary_tokens_canonical doc ->
    documentary_tokens_sound doc.
Proof.
  intros doc Hcanonical.
  unfold documentary_tokens_canonical in Hcanonical.
  unfold documentary_tokens_sound.
  induction Hcanonical.
  - constructor.
  - constructor.
    + apply entry_tokens_canonical_sound.
      exact H.
    + exact IHHcanonical.
Qed.

Lemma documentary_entries_align :
  forall doc,
    documentary_tablet_well_formed doc ->
    length (tablet_lines (documentary_semantics doc)) =
    length (documentary_entries doc).
Proof.
  intros doc [_ [_ [_ [_ [_ Halign]]]]].
  apply Forall2_length in Halign.
  exact Halign.
Qed.

Lemma documentary_support_has_shape :
  forall doc,
    documentary_tablet_well_formed doc ->
    documentary_support doc = SupportTablet ->
    exists shape, documentary_shape doc = Some shape.
Proof.
  intros doc [_ [_ [Hsupport [_ [_ _]]]]] Hsupport_kind.
  unfold support_shape_consistent in Hsupport.
  rewrite Hsupport_kind in Hsupport.
  exact Hsupport.
Qed.

Lemma documentary_jn_is_page_shaped :
  forall doc,
    documentary_tablet_well_formed doc ->
    tablet_series_of (documentary_semantics doc) = Series_Jn ->
    documentary_shape doc = Some PageShaped.
Proof.
  intros doc [_ [_ [_ [_ [Hshape _]]]]] Hseries.
  unfold series_shape_compatible in Hshape.
  rewrite Hseries in Hshape.
  exact Hshape.
Qed.

Lemma consistent_entries_are_positive :
  forall lines entries,
    Forall2 inscribed_entry_consistent lines entries ->
    Forall (fun entry => (0 < aegean_numeral_value (entry_numerals entry))%nat) entries.
Proof.
  intros lines entries Halign.
  induction Halign.
  - constructor.
  - constructor.
    + eapply inscribed_entry_consistent_positive.
      exact H.
    + exact IHHalign.
Qed.

Lemma documentary_entries_positive :
  forall doc,
    documentary_tablet_well_formed doc ->
    Forall (fun entry => (0 < aegean_numeral_value (entry_numerals entry))%nat)
           (documentary_entries doc).
Proof.
  intros doc [_ [_ [_ [_ [_ Halign]]]]].
  eapply consistent_entries_are_positive.
  exact Halign.
Qed.

Lemma documentary_archive_lengths_align :
  forall dar,
    documentary_archive_well_formed dar ->
    length (documentary_documents dar) =
    length (archive_tablets (documentary_archive_semantics dar)).
Proof.
  intros dar [_ [_ [_ Halign]]].
  rewrite <- Halign.
  rewrite length_map.
  reflexivity.
Qed.

Lemma documentary_archive_all_documents_registered :
  forall dar,
    documentary_archive_well_formed dar ->
    Forall
      (fun doc =>
         tablet_registered_in (documentary_archive_semantics dar)
                              (documentary_semantics doc))
      (documentary_documents dar).
Proof.
  intros dar [Harchive [_ [_ Hmap]]].
  destruct Harchive as [_ Hregistered].
  apply Forall_forall.
  intros doc Hdoc.
  pose proof
    ((proj1
        (Forall_forall
           (fun tab =>
              tablet_registered_in (documentary_archive_semantics dar) tab /\
              tablet_well_formed tab)
           (archive_tablets (documentary_archive_semantics dar)))
        Hregistered
        (documentary_semantics doc))) as Hlookup.
  assert (Hin :
            In (documentary_semantics doc)
               (archive_tablets (documentary_archive_semantics dar))).
  { rewrite <- Hmap. apply in_map. exact Hdoc. }
  specialize (Hlookup Hin).
  exact (proj1 Hlookup).
Qed.

Theorem tablet_balance_append_line :
  forall tracked tab line,
    tablet_balance tracked (append_line tab line) =
    (tablet_balance tracked tab + line_effect tracked line)%Z.
Proof.
  intros tracked tab line.
  unfold tablet_balance, append_line.
  simpl.
  rewrite map_app.
  simpl.
  rewrite fold_right_app.
  simpl.
  remember (map (line_effect tracked) (tablet_lines tab)) as effects.
  clear Heqeffects.
  induction effects as [|effect effects IHeffects]; simpl; lia.
Qed.

Theorem register_tablet_preserves_archive_well_formed :
  forall ar tab,
    archive_well_formed ar ->
    tablet_registered_in ar tab ->
    tablet_well_formed tab ->
    ~ In (tablet_identifier tab) (map tablet_identifier (archive_tablets ar)) ->
    archive_well_formed (register_tablet ar tab).
Proof.
  intros ar tab [Hnodup Htabs] Hregistered Hwf Hfresh.
  unfold archive_well_formed.
  split.
  - unfold register_tablet. simpl.
    rewrite map_app. simpl.
    apply NoDup_snoc; assumption.
  - unfold register_tablet. simpl.
    rewrite Forall_app. split.
    + exact Htabs.
    + constructor.
      * split; assumption.
      * constructor.
Qed.

Theorem archive_balance_register_tablet :
  forall tracked ar tab,
    archive_balance tracked (register_tablet ar tab) =
    (archive_balance tracked ar + tablet_balance tracked tab)%Z.
Proof.
  intros tracked ar tab.
  unfold archive_balance, register_tablet.
  simpl.
  rewrite map_app.
  simpl.
  rewrite fold_right_app.
  simpl.
  remember (map (tablet_balance tracked) (archive_tablets ar)) as balances.
  clear Heqbalances.
  induction balances as [|balance balances IHbalances]; simpl; lia.
Qed.

Definition qty4 : quantity.
Proof.
  refine {| quantity_value := 4 |}.
  lia.
Defined.

Definition qty7 : quantity.
Proof.
  refine {| quantity_value := 7 |}.
  lia.
Defined.

Definition qty12 : quantity.
Proof.
  refine {| quantity_value := 12 |}.
  lia.
Defined.

Definition qty15 : quantity.
Proof.
  refine {| quantity_value := 15 |}.
  lia.
Defined.

Definition scribe_1 : scribe_id := {| scribe_serial := 1 |}.
Definition scribe_2 : scribe_id := {| scribe_serial := 2 |}.
Definition person_1 : person_id := {| person_serial := 1 |}.
Definition seal_1 : seal_id := {| seal_serial := 1 |}.
Definition place_storehouse : place_id := {| place_serial := 10 |}.
Definition place_workshop : place_id := {| place_serial := 11 |}.
Definition place_archive_annex : place_id := {| place_serial := 12 |}.
Definition collective_1 : collective_id := {| collective_serial := 1 |}.

Definition barley_receipt : line_item :=
  {|
    line_number := 1;
    line_subject := NamedWorker person_1 CollectorRole;
    line_target := place_storehouse;
    line_genre := ReceiptRecord;
    line_direction := Incoming;
    line_commodity := Barley;
    line_quantity := qty12;
    line_seals := []
  |}.

Definition barley_allocation : line_item :=
  {|
    line_number := 2;
    line_subject := CollectiveLabor collective_1;
    line_target := place_workshop;
    line_genre := AllocationRecord;
    line_direction := Outgoing;
    line_commodity := Barley;
    line_quantity := qty4;
    line_seals := [seal_1]
  |}.

Definition bronze_receipt : line_item :=
  {|
    line_number := 1;
    line_subject := AdministrativeOffice place_workshop;
    line_target := place_archive_annex;
    line_genre := ReceiptRecord;
    line_direction := Incoming;
    line_commodity := Bronze;
    line_quantity := qty7;
    line_seals := []
  |}.

Definition receipt_only_tablet : tablet :=
  {|
    tablet_identifier := {| tablet_serial := 1 |};
    tablet_series_of := Series_Unclassified;
    tablet_scribe := scribe_1;
    tablet_archive_centre := Pylos;
    tablet_findspot := place_storehouse;
    tablet_lines := [barley_receipt]
  |}.

Definition sample_tablet : tablet :=
  append_line receipt_only_tablet barley_allocation.

Definition bronze_tablet : tablet :=
  {|
    tablet_identifier := {| tablet_serial := 2 |};
    tablet_series_of := Series_Jn;
    tablet_scribe := scribe_2;
    tablet_archive_centre := Pylos;
    tablet_findspot := place_archive_annex;
    tablet_lines := [bronze_receipt]
  |}.

Definition sample_archive : archive :=
  {|
    archive_centre := Pylos;
    archive_tablets := [sample_tablet]
  |}.

Definition expanded_archive : archive :=
  register_tablet sample_archive bronze_tablet.

Example receipt_only_tablet_well_formed :
  tablet_well_formed receipt_only_tablet.
Proof.
  unfold receipt_only_tablet, tablet_well_formed.
  split.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - split.
    + constructor.
      * unfold positive_line_number. simpl. lia.
      * constructor.
    + constructor.
      * simpl. left. reflexivity.
      * constructor.
Qed.

Example sample_tablet_well_formed :
  tablet_well_formed sample_tablet.
Proof.
  unfold sample_tablet.
  apply append_line_preserves_tablet_well_formed.
  - exact receipt_only_tablet_well_formed.
  - unfold positive_line_number. simpl. lia.
  - simpl. right. discriminate.
  - simpl. intros [Heq | []]. inversion Heq.
Qed.

Example bronze_tablet_well_formed :
  tablet_well_formed bronze_tablet.
Proof.
  unfold bronze_tablet, tablet_well_formed.
  split.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - split.
    + constructor.
      * unfold positive_line_number. simpl. lia.
      * constructor.
    + constructor.
      * simpl. left. reflexivity.
      * constructor.
Qed.

Example sample_archive_well_formed :
  archive_well_formed sample_archive.
Proof.
  unfold sample_archive, archive_well_formed.
  split.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - constructor.
    + split.
      * reflexivity.
      * exact sample_tablet_well_formed.
    + constructor.
Qed.

Example expanded_archive_well_formed :
  archive_well_formed expanded_archive.
Proof.
  unfold expanded_archive.
  apply register_tablet_preserves_archive_well_formed.
  - exact sample_archive_well_formed.
  - reflexivity.
  - exact bronze_tablet_well_formed.
  - simpl. intros [Heq | []]. inversion Heq.
Qed.

Example sample_tablet_barley_balance :
  tablet_balance Barley sample_tablet = 8%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Example sample_archive_barley_balance :
  archive_balance Barley sample_archive = 8%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Example expanded_archive_bronze_balance :
  archive_balance Bronze expanded_archive = 7%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Example expanded_archive_bronze_balance_by_registration :
  archive_balance Bronze expanded_archive =
  (archive_balance Bronze sample_archive + tablet_balance Bronze bronze_tablet)%Z.
Proof.
  unfold expanded_archive.
  apply archive_balance_register_tablet.
Qed.

Example bronze_tablet_series_compatible :
  tablet_series_compatible bronze_tablet.
Proof.
  unfold bronze_tablet, tablet_series_compatible, line_fits_series.
  simpl. constructor.
  - exact I.
  - constructor.
Qed.

Definition bronze_issue : line_item :=
  {|
    line_number := 2;
    line_subject := NamedWorker person_1 SmithRole;
    line_target := place_workshop;
    line_genre := AllocationRecord;
    line_direction := Outgoing;
    line_commodity := Bronze;
    line_quantity := qty4;
    line_seals := [seal_1]
  |}.

Definition sheep_inventory : line_item :=
  {|
    line_number := 1;
    line_subject := AdministrativeOffice place_storehouse;
    line_target := place_storehouse;
    line_genre := InventoryRecord;
    line_direction := Incoming;
    line_commodity := SheepStock;
    line_quantity := qty15;
    line_seals := []
  |}.

Definition jn_semantic_tablet : tablet :=
  {|
    tablet_identifier := {| tablet_serial := 3 |};
    tablet_series_of := Series_Jn;
    tablet_scribe := scribe_2;
    tablet_archive_centre := Pylos;
    tablet_findspot := place_workshop;
    tablet_lines := [bronze_receipt; bronze_issue]
  |}.

Definition jn_seed_tablet : tablet :=
  {|
    tablet_identifier := {| tablet_serial := 3 |};
    tablet_series_of := Series_Jn;
    tablet_scribe := scribe_2;
    tablet_archive_centre := Pylos;
    tablet_findspot := place_workshop;
    tablet_lines := [bronze_receipt]
  |}.

Definition cn_semantic_tablet : tablet :=
  {|
    tablet_identifier := {| tablet_serial := 4 |};
    tablet_series_of := Series_Cn;
    tablet_scribe := scribe_1;
    tablet_archive_centre := Pylos;
    tablet_findspot := place_storehouse;
    tablet_lines := [sheep_inventory]
  |}.

Definition bronze_receipt_entry : inscribed_entry :=
  {|
    entry_tokens :=
      [ TokenIdeogram IdeogramBronze;
        TokenNumber NumberSeven;
        TokenMeasure WeightBaseUnit ];
    entry_ideogram := Some IdeogramBronze;
    entry_numerals := [NumberSeven];
    entry_measure := Some WeightBaseUnit
  |}.

Definition bronze_issue_entry : inscribed_entry :=
  {|
    entry_tokens :=
      [ TokenSyllabogram (BasicSign SignKa);
        TokenIdeogram IdeogramBronze;
        TokenNumber NumberFour;
        TokenMeasure WeightBaseUnit ];
    entry_ideogram := Some IdeogramBronze;
    entry_numerals := [NumberFour];
    entry_measure := Some WeightBaseUnit
  |}.

Definition sheep_inventory_entry : inscribed_entry :=
  {|
    entry_tokens :=
      [ TokenIdeogram IdeogramEwe;
        TokenNumber NumberTen;
        TokenNumber NumberFive ];
    entry_ideogram := Some IdeogramEwe;
    entry_numerals := [NumberTen; NumberFive];
    entry_measure := None
  |}.

Definition jn_document : documentary_tablet :=
  {|
    documentary_semantics := jn_semantic_tablet;
    documentary_site := SitePylos;
    documentary_support := SupportTablet;
    documentary_shape := Some PageShaped;
    documentary_entries := [bronze_receipt_entry; bronze_issue_entry]
  |}.

Definition cn_document : documentary_tablet :=
  {|
    documentary_semantics := cn_semantic_tablet;
    documentary_site := SitePylos;
    documentary_support := SupportTablet;
    documentary_shape := Some LeafShaped;
    documentary_entries := [sheep_inventory_entry]
  |}.

Definition jn_document_seed : documentary_tablet :=
  {|
    documentary_semantics := jn_seed_tablet;
    documentary_site := SitePylos;
    documentary_support := SupportTablet;
    documentary_shape := Some PageShaped;
    documentary_entries := [bronze_receipt_entry]
  |}.

Definition pylos_jn_archive : archive :=
  {|
    archive_centre := Pylos;
    archive_tablets := [jn_semantic_tablet]
  |}.

Definition pylos_semantic_archive : archive :=
  register_tablet pylos_jn_archive cn_semantic_tablet.

Definition pylos_documentary_archive : documentary_archive :=
  {|
    documentary_archive_semantics := pylos_semantic_archive;
    documentary_documents := [jn_document; cn_document]
  |}.

Example jn_semantic_tablet_well_formed :
  tablet_well_formed jn_semantic_tablet.
Proof.
  unfold jn_semantic_tablet, tablet_well_formed.
  split.
  - simpl. constructor.
    + intros [Heq | []]. inversion Heq.
    + constructor.
      * intros Hin. inversion Hin.
      * constructor.
  - split.
    + repeat constructor; unfold positive_line_number; simpl; lia.
    + constructor.
      * simpl. left. reflexivity.
      * constructor.
        -- simpl. right. discriminate.
        -- constructor.
Qed.

Example jn_semantic_tablet_series_compatible :
  tablet_series_compatible jn_semantic_tablet.
Proof.
  unfold jn_semantic_tablet, tablet_series_compatible, line_fits_series.
  simpl. constructor.
  - exact I.
  - constructor.
    + exact I.
    + constructor.
Qed.

Example cn_semantic_tablet_well_formed :
  tablet_well_formed cn_semantic_tablet.
Proof.
  unfold cn_semantic_tablet, tablet_well_formed.
  split.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - split.
    + constructor.
      * unfold positive_line_number. simpl. lia.
      * constructor.
    + constructor.
      * simpl. left. reflexivity.
      * constructor.
Qed.

Example cn_semantic_tablet_series_compatible :
  tablet_series_compatible cn_semantic_tablet.
Proof.
  unfold cn_semantic_tablet, tablet_series_compatible, line_fits_series.
  simpl. constructor.
  - exact I.
  - constructor.
Qed.

Example bronze_receipt_entry_consistent :
  inscribed_entry_consistent bronze_receipt bronze_receipt_entry.
Proof.
  unfold inscribed_entry_consistent, bronze_receipt, bronze_receipt_entry.
  simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + left. reflexivity.
Qed.

Example bronze_issue_entry_consistent :
  inscribed_entry_consistent bronze_issue bronze_issue_entry.
Proof.
  unfold inscribed_entry_consistent, bronze_issue, bronze_issue_entry.
  simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + left. reflexivity.
Qed.

Example sheep_inventory_entry_consistent :
  inscribed_entry_consistent sheep_inventory sheep_inventory_entry.
Proof.
  unfold inscribed_entry_consistent, sheep_inventory, sheep_inventory_entry.
  simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + exact I.
Qed.

Example bronze_receipt_entry_tokens_realize_metadata :
  entry_tokens_realize_metadata bronze_receipt_entry.
Proof.
  unfold entry_tokens_realize_metadata, bronze_receipt_entry.
  simpl. repeat split; reflexivity.
Qed.

Example bronze_issue_entry_tokens_realize_metadata :
  entry_tokens_realize_metadata bronze_issue_entry.
Proof.
  unfold entry_tokens_realize_metadata, bronze_issue_entry.
  simpl. repeat split; reflexivity.
Qed.

Example sheep_inventory_entry_tokens_realize_metadata :
  entry_tokens_realize_metadata sheep_inventory_entry.
Proof.
  unfold entry_tokens_realize_metadata, sheep_inventory_entry.
  simpl. repeat split; reflexivity.
Qed.

Example bronze_receipt_entry_tokens_canonical :
  entry_tokens_canonical bronze_receipt_entry.
Proof.
  unfold entry_tokens_canonical, bronze_receipt_entry.
  simpl. repeat split; reflexivity.
Qed.

Example bronze_issue_entry_tokens_canonical :
  entry_tokens_canonical bronze_issue_entry.
Proof.
  unfold entry_tokens_canonical, bronze_issue_entry.
  simpl. repeat split; reflexivity.
Qed.

Example sheep_inventory_entry_tokens_canonical :
  entry_tokens_canonical sheep_inventory_entry.
Proof.
  unfold entry_tokens_canonical, sheep_inventory_entry.
  simpl. repeat split; reflexivity.
Qed.

Example jn_seed_tablet_well_formed :
  tablet_well_formed jn_seed_tablet.
Proof.
  unfold jn_seed_tablet, tablet_well_formed.
  split.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - split.
    + constructor.
      * unfold positive_line_number. simpl. lia.
      * constructor.
    + constructor.
      * simpl. left. reflexivity.
      * constructor.
Qed.

Example jn_seed_tablet_series_compatible :
  tablet_series_compatible jn_seed_tablet.
Proof.
  unfold jn_seed_tablet, tablet_series_compatible, line_fits_series.
  simpl. constructor.
  - exact I.
  - constructor.
Qed.

Example jn_document_seed_well_formed :
  documentary_tablet_well_formed jn_document_seed.
Proof.
  unfold documentary_tablet_well_formed, jn_document_seed.
  split.
  - exact jn_seed_tablet_well_formed.
  - split.
    + exact jn_seed_tablet_series_compatible.
    + split.
      * exists PageShaped. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ constructor.
              ** exact bronze_receipt_entry_consistent.
              ** constructor.
Qed.

Example jn_document_seed_tokens_sound :
  documentary_tokens_sound jn_document_seed.
Proof.
  unfold documentary_tokens_sound, jn_document_seed.
  constructor.
  - exact bronze_receipt_entry_tokens_realize_metadata.
  - constructor.
Qed.

Example jn_document_seed_tokens_canonical :
  documentary_tokens_canonical jn_document_seed.
Proof.
  unfold documentary_tokens_canonical, jn_document_seed.
  constructor.
  - exact bronze_receipt_entry_tokens_canonical.
  - constructor.
Qed.

Example jn_document_constructed_by_append :
  append_documentary_entry jn_document_seed bronze_issue bronze_issue_entry = jn_document.
Proof.
  reflexivity.
Qed.

Example jn_document_constructed_well_formed :
  documentary_tablet_well_formed
    (append_documentary_entry jn_document_seed bronze_issue bronze_issue_entry).
Proof.
  apply append_documentary_entry_preserves_documentary_tablet_well_formed.
  - exact jn_document_seed_well_formed.
  - unfold positive_line_number. simpl. lia.
  - simpl. right. discriminate.
  - simpl. intros [Heq | []]. inversion Heq.
  - unfold line_fits_series. simpl. exact I.
  - exact bronze_issue_entry_consistent.
Qed.

Example jn_document_constructed_tokens_sound :
  documentary_tokens_sound
    (append_documentary_entry jn_document_seed bronze_issue bronze_issue_entry).
Proof.
  apply append_documentary_entry_preserves_tokens_sound.
  - exact jn_document_seed_tokens_sound.
  - exact bronze_issue_entry_tokens_realize_metadata.
Qed.

Example jn_document_constructed_tokens_canonical :
  documentary_tokens_canonical
    (append_documentary_entry jn_document_seed bronze_issue bronze_issue_entry).
Proof.
  apply append_documentary_entry_preserves_tokens_canonical.
  - exact jn_document_seed_tokens_canonical.
  - exact bronze_issue_entry_tokens_canonical.
Qed.

Example bronze_issue_entry_positive :
  (0 < aegean_numeral_value (entry_numerals bronze_issue_entry))%nat.
Proof.
  vm_compute.
  lia.
Qed.

Example jn_document_well_formed :
  documentary_tablet_well_formed jn_document.
Proof.
  unfold documentary_tablet_well_formed, jn_document.
  split.
  - exact jn_semantic_tablet_well_formed.
  - split.
    + exact jn_semantic_tablet_series_compatible.
    + split.
      * exists PageShaped. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ constructor.
              ** exact bronze_receipt_entry_consistent.
              ** constructor.
                 --- exact bronze_issue_entry_consistent.
                 --- constructor.
Qed.

Example jn_document_tokens_sound :
  documentary_tokens_sound jn_document.
Proof.
  unfold documentary_tokens_sound, jn_document.
  constructor.
  - exact bronze_receipt_entry_tokens_realize_metadata.
  - constructor.
    + exact bronze_issue_entry_tokens_realize_metadata.
    + constructor.
Qed.

Example jn_document_tokens_canonical :
  documentary_tokens_canonical jn_document.
Proof.
  unfold documentary_tokens_canonical, jn_document.
  constructor.
  - exact bronze_receipt_entry_tokens_canonical.
  - constructor.
    + exact bronze_issue_entry_tokens_canonical.
    + constructor.
Qed.

Example cn_document_well_formed :
  documentary_tablet_well_formed cn_document.
Proof.
  unfold documentary_tablet_well_formed, cn_document.
  split.
  - exact cn_semantic_tablet_well_formed.
  - split.
    + exact cn_semantic_tablet_series_compatible.
    + split.
      * exists LeafShaped. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ exact I.
           ++ constructor.
              ** exact sheep_inventory_entry_consistent.
              ** constructor.
Qed.

Example cn_document_tokens_sound :
  documentary_tokens_sound cn_document.
Proof.
  unfold documentary_tokens_sound, cn_document.
  constructor.
  - exact sheep_inventory_entry_tokens_realize_metadata.
  - constructor.
Qed.

Example cn_document_tokens_canonical :
  documentary_tokens_canonical cn_document.
Proof.
  unfold documentary_tokens_canonical, cn_document.
  constructor.
  - exact sheep_inventory_entry_tokens_canonical.
  - constructor.
Qed.

Example jn_document_canonical_implies_sound :
  documentary_tokens_sound jn_document.
Proof.
  apply documentary_tokens_canonical_sound.
  exact jn_document_tokens_canonical.
Qed.

Example pylos_jn_archive_well_formed :
  archive_well_formed pylos_jn_archive.
Proof.
  unfold pylos_jn_archive, archive_well_formed.
  split.
  - simpl. constructor.
    + intros Hin. inversion Hin.
    + constructor.
  - constructor.
    + split.
      * reflexivity.
      * exact jn_semantic_tablet_well_formed.
    + constructor.
Qed.

Example pylos_semantic_archive_well_formed :
  archive_well_formed pylos_semantic_archive.
Proof.
  unfold pylos_semantic_archive.
  apply register_tablet_preserves_archive_well_formed.
  - exact pylos_jn_archive_well_formed.
  - reflexivity.
  - exact cn_semantic_tablet_well_formed.
  - simpl. intros [Heq | []]. inversion Heq.
Qed.

Example pylos_documentary_archive_well_formed :
  documentary_archive_well_formed pylos_documentary_archive.
Proof.
  unfold documentary_archive_well_formed, pylos_documentary_archive.
  split.
  - exact pylos_semantic_archive_well_formed.
  - split.
    + constructor.
      * exact jn_document_well_formed.
      * constructor.
        -- exact cn_document_well_formed.
        -- constructor.
    + split.
      * constructor.
        -- exact jn_document_tokens_sound.
        -- constructor.
           ++ exact cn_document_tokens_sound.
           ++ constructor.
      * reflexivity.
Qed.

Example pylos_documentary_archive_lengths_align :
  length (documentary_documents pylos_documentary_archive) =
  length (archive_tablets (documentary_archive_semantics pylos_documentary_archive)).
Proof.
  apply documentary_archive_lengths_align.
  exact pylos_documentary_archive_well_formed.
Qed.

Example pylos_documentary_archive_documents_registered :
  Forall
    (fun doc =>
       tablet_registered_in (documentary_archive_semantics pylos_documentary_archive)
                            (documentary_semantics doc))
    (documentary_documents pylos_documentary_archive).
Proof.
  apply documentary_archive_all_documents_registered.
  exact pylos_documentary_archive_well_formed.
Qed.

Example pylos_documentary_archive_bronze_balance :
  archive_balance Bronze (documentary_archive_semantics pylos_documentary_archive) = 3%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Example pylos_documentary_archive_sheep_balance :
  archive_balance SheepStock (documentary_archive_semantics pylos_documentary_archive) = 15%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Example jn_document_entries_align :
  length (tablet_lines (documentary_semantics jn_document)) =
  length (documentary_entries jn_document).
Proof.
  apply documentary_entries_align.
  exact jn_document_well_formed.
Qed.

Example jn_document_has_shape :
  exists shape, documentary_shape jn_document = Some shape.
Proof.
  apply documentary_support_has_shape.
  - exact jn_document_well_formed.
  - reflexivity.
Qed.

Example jn_document_is_page_shaped :
  documentary_shape jn_document = Some PageShaped.
Proof.
  apply documentary_jn_is_page_shaped.
  - exact jn_document_well_formed.
  - reflexivity.
Qed.

Example jn_document_entries_positive :
  Forall (fun entry => (0 < aegean_numeral_value (entry_numerals entry))%nat)
         (documentary_entries jn_document).
Proof.
  apply documentary_entries_positive.
  exact jn_document_well_formed.
Qed.

Example jn_document_bronze_balance :
  tablet_balance Bronze (documentary_semantics jn_document) = 3%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Example cn_document_sheep_balance :
  tablet_balance SheepStock (documentary_semantics cn_document) = 15%Z.
Proof.
  vm_compute. reflexivity.
Qed.

Scheme Equality for archive_site.

Inductive damos_hand :=
| DamosHand1
| DamosHand2
| DamosHand8
| DamosHand21
| DamosHand31
| DamosHand42
| DamosHandCii.

Scheme Equality for damos_hand.

Inductive pylos_find_area :=
| PylosAreaChasm
| PylosAreaChasmAndRoom7_1
| PylosAreaChasmAndRoom7
| PylosAreaRoom2
| PylosAreaRoom7
| PylosAreaRoom7AndChasm
| PylosAreaRoom7AndChasmRoom7_1
| PylosAreaRoom8
| PylosAreaRoom8AndChasm
| PylosAreaRoom8AndRoom7
| PylosAreaRoom99
| PylosAreaSouthWestChasm.

Scheme Equality for pylos_find_area.

Definition archive_site_eqb (lhs rhs : archive_site) : bool :=
  if archive_site_eq_dec lhs rhs then true else false.

Definition damos_hand_eqb (lhs rhs : damos_hand) : bool :=
  if damos_hand_eq_dec lhs rhs then true else false.

Definition pylos_find_area_eqb (lhs rhs : pylos_find_area) : bool :=
  if pylos_find_area_eq_dec lhs rhs then true else false.

Definition list_subsetb {A : Type}
  (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  forallb (fun x => existsb (eqb x) ys) xs.

Fixpoint nodup_nat_listb (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest =>
      negb (existsb (Nat.eqb x) rest) && nodup_nat_listb rest
  end.

Record damos_tablet_snapshot := {
  damos_snapshot_id : nat;
  damos_snapshot_site : archive_site;
  damos_snapshot_series : tablet_series;
  damos_snapshot_number : nat;
  damos_snapshot_set : nat;
  damos_snapshot_hand_candidates : list damos_hand;
  damos_snapshot_stylus_candidates : list nat;
  damos_snapshot_find_area : pylos_find_area;
  damos_snapshot_line_count : nat;
  damos_snapshot_has_aes : bool;
  damos_snapshot_has_bos : bool;
  damos_snapshot_has_ovis : bool;
  damos_snapshot_has_cap : bool
}.

Definition mk_damos_snapshot
  (snapshot_id : nat)
  (snapshot_series : tablet_series)
  (snapshot_number : nat)
  (snapshot_set : nat)
  (snapshot_hands : list damos_hand)
  (snapshot_styli : list nat)
  (snapshot_find_area : pylos_find_area)
  (snapshot_line_count : nat)
  (snapshot_has_aes snapshot_has_bos snapshot_has_ovis snapshot_has_cap : bool)
  : damos_tablet_snapshot :=
  {|
    damos_snapshot_id := snapshot_id;
    damos_snapshot_site := SitePylos;
    damos_snapshot_series := snapshot_series;
    damos_snapshot_number := snapshot_number;
    damos_snapshot_set := snapshot_set;
    damos_snapshot_hand_candidates := snapshot_hands;
    damos_snapshot_stylus_candidates := snapshot_styli;
    damos_snapshot_find_area := snapshot_find_area;
    damos_snapshot_line_count := snapshot_line_count;
    damos_snapshot_has_aes := snapshot_has_aes;
    damos_snapshot_has_bos := snapshot_has_bos;
    damos_snapshot_has_ovis := snapshot_has_ovis;
    damos_snapshot_has_cap := snapshot_has_cap
  |}.

Definition damos_pylos_jn_cn_snapshots : list damos_tablet_snapshot :=
[
  mk_damos_snapshot 4681 Series_Jn 310 1 [DamosHand2] [310] PylosAreaRoom8 17 true false false false;
  mk_damos_snapshot 4682 Series_Jn 320 1 [DamosHand2] [310] PylosAreaRoom8 16 true false false false;
  mk_damos_snapshot 4683 Series_Jn 389 1 [DamosHand2] [310] PylosAreaRoom8 13 true false false false;
  mk_damos_snapshot 4684 Series_Jn 410 1 [DamosHand2] [310] PylosAreaRoom8 9 true false false false;
  mk_damos_snapshot 4685 Series_Jn 415 1 [DamosHand2] [310] PylosAreaRoom8 13 true false false false;
  mk_damos_snapshot 4686 Series_Jn 431 1 [DamosHand2] [310] PylosAreaRoom8 26 true false false false;
  mk_damos_snapshot 4687 Series_Jn 478 1 [DamosHand2] [310] PylosAreaRoom8 12 true false false false;
  mk_damos_snapshot 4688 Series_Jn 601 1 [DamosHand2] [310] PylosAreaRoom8 16 true false false false;
  mk_damos_snapshot 4689 Series_Jn 605 1 [DamosHand2] [310] PylosAreaRoom7AndChasmRoom7_1 11 true false false false;
  mk_damos_snapshot 4690 Series_Jn 658 2 [DamosHand21] [658] PylosAreaRoom7AndChasm 13 true false false false;
  mk_damos_snapshot 4691 Series_Jn 692 1 [DamosHand2] [310] PylosAreaRoom7 8 true false false false;
  mk_damos_snapshot 4692 Series_Jn 693 1 [DamosHand2] [310] PylosAreaRoom7 13 true false false false;
  mk_damos_snapshot 4693 Series_Jn 706 2 [DamosHand21] [658] PylosAreaRoom7AndChasm 30 true false false false;
  mk_damos_snapshot 4694 Series_Jn 725 1 [DamosHand2] [310] PylosAreaRoom7 26 true false false false;
  mk_damos_snapshot 4695 Series_Jn 750 1 [DamosHand2] [310] PylosAreaChasm 13 true false false false;
  mk_damos_snapshot 4696 Series_Jn 829 1 [DamosHand2] [310] PylosAreaRoom8AndChasm 24 true false false false;
  mk_damos_snapshot 4697 Series_Jn 832 1 [DamosHand2] [310] PylosAreaChasmAndRoom7_1 17 true false false false;
  mk_damos_snapshot 4698 Series_Jn 845 1 [DamosHand2] [310] PylosAreaChasm 14 true false false false;
  mk_damos_snapshot 4699 Series_Jn 881 1 [DamosHand2] [310] PylosAreaRoom2 13 true false false false;
  mk_damos_snapshot 4701 Series_Jn 927 1 [DamosHand2] [310] PylosAreaChasmAndRoom7 13 true false false false;
  mk_damos_snapshot 4372 Series_Cn 3 2 [DamosHand1] [608] PylosAreaRoom8 9 false true false false;
  mk_damos_snapshot 4373 Series_Cn 4 5 [DamosHand21] [4] PylosAreaRoom8 11 false false true false;
  mk_damos_snapshot 4374 Series_Cn 40 5 [DamosHand21] [4] PylosAreaRoom8 16 false false true false;
  mk_damos_snapshot 4375 Series_Cn 45 5 [DamosHand1; DamosHand21] [4; 719] PylosAreaRoom8 16 false false true true;
  mk_damos_snapshot 4376 Series_Cn 131 1 [DamosHand1] [131] PylosAreaRoom8 15 false false true true;
  mk_damos_snapshot 4377 Series_Cn 155 5 [DamosHand21] [155] PylosAreaChasm 3 false false true false;
  mk_damos_snapshot 5094 Series_Cn 200 6 [DamosHand8] [] PylosAreaRoom8 2 false false false false;
  mk_damos_snapshot 4378 Series_Cn 202 1 [DamosHand1] [131] PylosAreaRoom8 5 false false true true;
  mk_damos_snapshot 4380 Series_Cn 254 5 [DamosHand21] [4] PylosAreaRoom8 13 false false true false;
  mk_damos_snapshot 4382 Series_Cn 285 1 [DamosHand1] [131] PylosAreaRoom8 14 false false true true;
  mk_damos_snapshot 4383 Series_Cn 286 3 [DamosHand1] [719] PylosAreaRoom8 2 false false false false;
  mk_damos_snapshot 4384 Series_Cn 314 3 [DamosHand1] [] PylosAreaRoom8 3 false false true false;
  mk_damos_snapshot 4385 Series_Cn 328 1 [DamosHand1] [131] PylosAreaRoom8 16 false false true true;
  mk_damos_snapshot 4386 Series_Cn 418 0 [DamosHand42] [] PylosAreaRoom8 9 false true true true;
  mk_damos_snapshot 4387 Series_Cn 436 1 [DamosHand1; DamosHandCii] [131] PylosAreaRoom8 10 false false true true;
  mk_damos_snapshot 4388 Series_Cn 437 3 [DamosHand1] [719] PylosAreaRoom8 6 false false true false;
  mk_damos_snapshot 4389 Series_Cn 440 1 [DamosHand1] [] PylosAreaRoom8 10 false false false false;
  mk_damos_snapshot 4390 Series_Cn 441 1 [DamosHand1] [131] PylosAreaRoom8 5 false false false true;
  mk_damos_snapshot 4391 Series_Cn 453 4 [DamosHand1] [925] PylosAreaRoom8AndChasm 2 false false false true;
  mk_damos_snapshot 4392 Series_Cn 485 3 [DamosHand1] [719] PylosAreaRoom8 19 false false true false;
  mk_damos_snapshot 4393 Series_Cn 491 1 [DamosHand1] [131] PylosAreaRoom8 8 false false true true;
  mk_damos_snapshot 4394 Series_Cn 570 4 [DamosHand1] [925] PylosAreaRoom8 5 false false false false;
  mk_damos_snapshot 4395 Series_Cn 595 5 [DamosHand1; DamosHand21] [4] PylosAreaRoom8 8 false false true false;
  mk_damos_snapshot 4396 Series_Cn 599 5 [DamosHand1; DamosHand21] [4; 719] PylosAreaRoom8 9 false false false true;
  mk_damos_snapshot 4397 Series_Cn 600 5 [DamosHand21] [4] PylosAreaRoom8 16 false false true true;
  mk_damos_snapshot 4398 Series_Cn 608 2 [DamosHand1] [608] PylosAreaRoom7 11 false false false false;
  mk_damos_snapshot 4399 Series_Cn 643 3 [DamosHand1] [719] PylosAreaChasmAndRoom7 9 false false false true;
  mk_damos_snapshot 4400 Series_Cn 655 3 [DamosHand1; DamosHand21] [4; 719] PylosAreaRoom7 20 false false true false;
  mk_damos_snapshot 4401 Series_Cn 702 3 [DamosHand1] [719] PylosAreaRoom7 6 false false true true;
  mk_damos_snapshot 4402 Series_Cn 719 3 [DamosHand1] [719] PylosAreaRoom7AndChasm 13 false false true false;
  mk_damos_snapshot 4403 Series_Cn 925 4 [DamosHand1] [925] PylosAreaRoom8AndRoom7 3 false false false false;
  mk_damos_snapshot 4404 Series_Cn 938 5 [DamosHand21] [4] PylosAreaChasm 4 false false false false;
  mk_damos_snapshot 4405 Series_Cn 962 5 [DamosHand21] [4] PylosAreaChasm 3 false false false false;
  mk_damos_snapshot 4406 Series_Cn 1059 3 [DamosHand1] [719] PylosAreaRoom8 3 false false false false;
  mk_damos_snapshot 4407 Series_Cn 1197 1 [DamosHand1] [131] PylosAreaSouthWestChasm 6 false false true false;
  mk_damos_snapshot 4408 Series_Cn 1286 0 [DamosHandCii] [] PylosAreaRoom99 5 false false true true;
  mk_damos_snapshot 4409 Series_Cn 1287 0 [DamosHand31] [] PylosAreaRoom99 12 false false false true
].

Definition snapshot_of_series
  (series : tablet_series) (snapshot : damos_tablet_snapshot) : bool :=
  if tablet_series_eq_dec (damos_snapshot_series snapshot) series then true else false.

Definition snapshot_of_site
  (site : archive_site) (snapshot : damos_tablet_snapshot) : bool :=
  archive_site_eqb (damos_snapshot_site snapshot) site.

Definition snapshot_in_find_area
  (area : pylos_find_area) (snapshot : damos_tablet_snapshot) : bool :=
  pylos_find_area_eqb (damos_snapshot_find_area snapshot) area.

Definition count_damos_snapshots
  (predicate : damos_tablet_snapshot -> bool)
  (snapshots : list damos_tablet_snapshot) : nat :=
  length (filter predicate snapshots).

Definition all_damos_snapshots
  (predicate : damos_tablet_snapshot -> bool)
  (snapshots : list damos_tablet_snapshot) : bool :=
  forallb predicate snapshots.

Definition damos_snapshots_of_series
  (series : tablet_series) (snapshots : list damos_tablet_snapshot) :
  list damos_tablet_snapshot :=
  filter (snapshot_of_series series) snapshots.

Definition sum_damos_line_counts (snapshots : list damos_tablet_snapshot) : nat :=
  fold_right Nat.add 0 (map damos_snapshot_line_count snapshots).

Definition max_damos_line_count (snapshots : list damos_tablet_snapshot) : nat :=
  fold_right Nat.max 0 (map damos_snapshot_line_count snapshots).

Definition snapshot_has_only_hands
  (allowed : list damos_hand) (snapshot : damos_tablet_snapshot) : bool :=
  list_subsetb damos_hand_eqb (damos_snapshot_hand_candidates snapshot) allowed.

Definition snapshot_has_only_styli
  (allowed : list nat) (snapshot : damos_tablet_snapshot) : bool :=
  list_subsetb Nat.eqb (damos_snapshot_stylus_candidates snapshot) allowed.

Definition snapshot_has_any_pastoral_marker
  (snapshot : damos_tablet_snapshot) : bool :=
  orb (damos_snapshot_has_bos snapshot)
      (orb (damos_snapshot_has_ovis snapshot)
           (damos_snapshot_has_cap snapshot)).

Definition snapshot_has_jn_marker_profile
  (snapshot : damos_tablet_snapshot) : bool :=
  andb (damos_snapshot_has_aes snapshot)
       (negb (snapshot_has_any_pastoral_marker snapshot)).

Definition snapshot_has_jn_hand_stylus_profile
  (snapshot : damos_tablet_snapshot) : bool :=
  orb (andb (snapshot_has_only_hands [DamosHand2] snapshot)
            (snapshot_has_only_styli [310] snapshot))
      (andb (snapshot_has_only_hands [DamosHand21] snapshot)
            (snapshot_has_only_styli [658] snapshot)).

Definition damos_pylos_jn_snapshots : list damos_tablet_snapshot :=
  damos_snapshots_of_series Series_Jn damos_pylos_jn_cn_snapshots.

Definition damos_pylos_cn_snapshots : list damos_tablet_snapshot :=
  damos_snapshots_of_series Series_Cn damos_pylos_jn_cn_snapshots.

Definition lookup_damos_snapshot_by_id
  (target : nat)
  (snapshots : list damos_tablet_snapshot) : option damos_tablet_snapshot :=
  find (fun snapshot => Nat.eqb (damos_snapshot_id snapshot) target) snapshots.

Definition damos_pylos_829_snapshot : option damos_tablet_snapshot :=
  lookup_damos_snapshot_by_id 4696 damos_pylos_jn_cn_snapshots.

Definition damos_pylos_131_snapshot : option damos_tablet_snapshot :=
  lookup_damos_snapshot_by_id 4376 damos_pylos_jn_cn_snapshots.

Example damos_pylos_attested_slice_count :
  length damos_pylos_jn_cn_snapshots = 57.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_count :
  length damos_pylos_jn_snapshots = 20.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_count :
  length damos_pylos_cn_snapshots = 37.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_all_sites_are_pylos :
  all_damos_snapshots (snapshot_of_site SitePylos) damos_pylos_jn_cn_snapshots = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_slice_ids_unique :
  nodup_nat_listb (map damos_snapshot_id damos_pylos_jn_cn_snapshots) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_numbers_unique :
  nodup_nat_listb (map damos_snapshot_number damos_pylos_jn_snapshots) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_numbers_unique :
  nodup_nat_listb (map damos_snapshot_number damos_pylos_cn_snapshots) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_marker_profile :
  all_damos_snapshots snapshot_has_jn_marker_profile damos_pylos_jn_snapshots = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_no_aes_markers :
  count_damos_snapshots damos_snapshot_has_aes damos_pylos_cn_snapshots = 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_ovis_marker_count :
  count_damos_snapshots damos_snapshot_has_ovis damos_pylos_cn_snapshots = 22.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_cap_marker_count :
  count_damos_snapshots damos_snapshot_has_cap damos_pylos_cn_snapshots = 16.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_bos_marker_count :
  count_damos_snapshots damos_snapshot_has_bos damos_pylos_cn_snapshots = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_any_pastoral_marker_count :
  count_damos_snapshots snapshot_has_any_pastoral_marker damos_pylos_cn_snapshots = 28.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_set_profile :
  all_damos_snapshots
    (fun snapshot =>
       andb (Nat.leb 1 (damos_snapshot_set snapshot))
            (Nat.leb (damos_snapshot_set snapshot) 2))
    damos_pylos_jn_snapshots = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_hand_stylus_profile :
  all_damos_snapshots
    snapshot_has_jn_hand_stylus_profile
    damos_pylos_jn_snapshots = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_primary_profile_count :
  count_damos_snapshots
    (fun snapshot =>
       andb (snapshot_has_only_hands [DamosHand2] snapshot)
            (snapshot_has_only_styli [310] snapshot))
    damos_pylos_jn_snapshots = 18.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_secondary_profile_count :
  count_damos_snapshots
    (fun snapshot =>
       andb (snapshot_has_only_hands [DamosHand21] snapshot)
            (snapshot_has_only_styli [658] snapshot))
    damos_pylos_jn_snapshots = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_room8_count :
  count_damos_snapshots
    (snapshot_in_find_area PylosAreaRoom8)
    damos_pylos_jn_cn_snapshots = 32.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_room8_count :
  count_damos_snapshots
    (snapshot_in_find_area PylosAreaRoom8)
    damos_pylos_jn_snapshots = 8.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_room8_count :
  count_damos_snapshots
    (snapshot_in_find_area PylosAreaRoom8)
    damos_pylos_cn_snapshots = 24.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_total_line_count :
  sum_damos_line_counts damos_pylos_jn_snapshots = 317.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_total_line_count :
  sum_damos_line_counts damos_pylos_cn_snapshots = 327.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_line_count_exceeds_jn :
  (sum_damos_line_counts damos_pylos_cn_snapshots >
   sum_damos_line_counts damos_pylos_jn_snapshots)%nat.
Proof.
  vm_compute. lia.
Qed.

Example damos_pylos_jn_max_line_count :
  max_damos_line_count damos_pylos_jn_snapshots = 30.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_max_line_count :
  max_damos_line_count damos_pylos_cn_snapshots = 20.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_jn_829_occurs_once :
  count_damos_snapshots
    (fun snapshot => Nat.eqb (damos_snapshot_id snapshot) 4696)
    damos_pylos_jn_cn_snapshots = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_829_snapshot_exact :
  damos_pylos_829_snapshot =
  Some
    (mk_damos_snapshot 4696 Series_Jn 829 1 [DamosHand2] [310]
                       PylosAreaRoom8AndChasm 24 true false false false).
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_cn_131_occurs_once :
  count_damos_snapshots
    (fun snapshot => Nat.eqb (damos_snapshot_id snapshot) 4376)
    damos_pylos_jn_cn_snapshots = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_pylos_131_snapshot_exact :
  damos_pylos_131_snapshot =
  Some
    (mk_damos_snapshot 4376 Series_Cn 131 1 [DamosHand1] [131]
                       PylosAreaRoom8 15 false false true true).
Proof.
  vm_compute. reflexivity.
Qed.

Inductive damos_collection :=
| CollectionKnossos
| CollectionPylos
| CollectionThebes
| CollectionMycenae
| CollectionTiryns
| CollectionKhania
| CollectionHagiosVasileios
| CollectionMidea
| CollectionDimini
| CollectionIklaina
| CollectionMedeon
| CollectionVolos
| CollectionSissi
| CollectionVasesArmeni
| CollectionVasesDimini
| CollectionVasesEleusis
| CollectionVasesGla
| CollectionVasesKhania
| CollectionVasesKnossos
| CollectionVasesKreusis
| CollectionVasesMallia
| CollectionVasesMamelouko
| CollectionVasesMidea
| CollectionVasesMycenae
| CollectionVasesPrinias
| CollectionVasesOrchomenos
| CollectionVasesSidon
| CollectionVasesThebes
| CollectionVasesTiryns.

Scheme Equality for damos_collection.

Record damos_collection_snapshot := {
  damos_collection_name : damos_collection;
  damos_collection_count : nat
}.

Definition mk_damos_collection_snapshot
  (name : damos_collection) (count : nat) : damos_collection_snapshot :=
  {|
    damos_collection_name := name;
    damos_collection_count := count
  |}.

Definition damos_collection_is_vase (collection : damos_collection) : bool :=
  match collection with
  | CollectionVasesArmeni
  | CollectionVasesDimini
  | CollectionVasesEleusis
  | CollectionVasesGla
  | CollectionVasesKhania
  | CollectionVasesKnossos
  | CollectionVasesKreusis
  | CollectionVasesMallia
  | CollectionVasesMamelouko
  | CollectionVasesMidea
  | CollectionVasesMycenae
  | CollectionVasesPrinias
  | CollectionVasesOrchomenos
  | CollectionVasesSidon
  | CollectionVasesThebes
  | CollectionVasesTiryns => true
  | _ => false
  end.

Definition damos_collection_census : list damos_collection_snapshot :=
[
  mk_damos_collection_snapshot CollectionKnossos 4224;
  mk_damos_collection_snapshot CollectionPylos 1004;
  mk_damos_collection_snapshot CollectionThebes 363;
  mk_damos_collection_snapshot CollectionMycenae 87;
  mk_damos_collection_snapshot CollectionTiryns 27;
  mk_damos_collection_snapshot CollectionKhania 8;
  mk_damos_collection_snapshot CollectionHagiosVasileios 5;
  mk_damos_collection_snapshot CollectionMidea 4;
  mk_damos_collection_snapshot CollectionDimini 1;
  mk_damos_collection_snapshot CollectionIklaina 1;
  mk_damos_collection_snapshot CollectionMedeon 1;
  mk_damos_collection_snapshot CollectionVolos 2;
  mk_damos_collection_snapshot CollectionSissi 1;
  mk_damos_collection_snapshot CollectionVasesArmeni 1;
  mk_damos_collection_snapshot CollectionVasesDimini 1;
  mk_damos_collection_snapshot CollectionVasesEleusis 1;
  mk_damos_collection_snapshot CollectionVasesGla 1;
  mk_damos_collection_snapshot CollectionVasesKhania 45;
  mk_damos_collection_snapshot CollectionVasesKnossos 4;
  mk_damos_collection_snapshot CollectionVasesKreusis 1;
  mk_damos_collection_snapshot CollectionVasesMallia 4;
  mk_damos_collection_snapshot CollectionVasesMamelouko 1;
  mk_damos_collection_snapshot CollectionVasesMidea 2;
  mk_damos_collection_snapshot CollectionVasesMycenae 20;
  mk_damos_collection_snapshot CollectionVasesPrinias 1;
  mk_damos_collection_snapshot CollectionVasesOrchomenos 1;
  mk_damos_collection_snapshot CollectionVasesSidon 1;
  mk_damos_collection_snapshot CollectionVasesThebes 75;
  mk_damos_collection_snapshot CollectionVasesTiryns 45
].

Definition sum_damos_collection_counts
  (collections : list damos_collection_snapshot) : nat :=
  fold_right Nat.add 0 (map damos_collection_count collections).

Definition lookup_damos_collection_count
  (target : damos_collection)
  (collections : list damos_collection_snapshot) : option nat :=
  match find
          (fun snapshot =>
             if damos_collection_eq_dec (damos_collection_name snapshot) target
             then true else false)
          collections with
  | Some snapshot => Some (damos_collection_count snapshot)
  | None => None
  end.

Definition filter_damos_collections_by_vase
  (is_vase : bool)
  (collections : list damos_collection_snapshot) :
  list damos_collection_snapshot :=
  filter
    (fun snapshot => Bool.eqb (damos_collection_is_vase (damos_collection_name snapshot))
                              is_vase)
    collections.

Example damos_collection_census_total :
  sum_damos_collection_counts damos_collection_census = 5932.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_collection_site_total :
  sum_damos_collection_counts
    (filter_damos_collections_by_vase false damos_collection_census) = 5728.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_collection_vase_total :
  sum_damos_collection_counts
    (filter_damos_collections_by_vase true damos_collection_census) = 204.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_collection_knossos_count :
  lookup_damos_collection_count CollectionKnossos damos_collection_census =
  Some 4224.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_collection_pylos_count :
  lookup_damos_collection_count CollectionPylos damos_collection_census =
  Some 1004.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_collection_thebes_count :
  lookup_damos_collection_count CollectionThebes damos_collection_census =
  Some 363.
Proof.
  vm_compute. reflexivity.
Qed.

Example damos_collection_major_order :
  match lookup_damos_collection_count CollectionKnossos damos_collection_census,
        lookup_damos_collection_count CollectionPylos damos_collection_census,
        lookup_damos_collection_count CollectionThebes damos_collection_census with
  | Some knossos_count, Some pylos_count, Some thebes_count =>
      (knossos_count > pylos_count /\ pylos_count > thebes_count)%nat
  | _, _, _ => False
  end.
Proof.
  vm_compute. lia.
Qed.
