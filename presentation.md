<!--!>
    TODO:
    - brief discussion of refinement types
      “they’re types refined by an SMT-checked proposition”
    - talk about limitations of SMT solvers
    - talk about linearisation
    - talk about liquid haskell
    - talk about overhead from F* encoding in Z3
    - talk about performance issues with Z3
    - talk about future work
    - talk about refinement types to rule out feeding tito into the network
      “there’s more uses to this approach, for instance, what happens when we feed this image into the network? well, according to our features, it’s got lots of grey, and no green… so it’s a cat! but that’s unfair, our network has never seen a raccoon…”
<---->

# [fit] Robustness as a Refinement Type

### [fit] *Wen Kokke*, Ekaterina Komendantskaya, and Daniel Kienitz

#### Lab for AI and Verification, Heriot-Watt University

---

^
So, imagine you’re me, and you’re bored on a Monday night, a couple of days before you have to give a talk… and you decide to try and train a neural network to classify which of your friends have cats, and which have dogs. You ask some friends for pictures of their pets, put together a dataset, and let a neural network have a go…

^
(That cutie on the bottom-right is my cat, by the way. Her name is Zaza.)

^
Anyway, these images are pretty big, like almost half a million pixels. Sure, we can deal with that, but for a neural network, that’s pretty big… so you’re more likely to present them with something like this…

![fit](pets.png)

---

^
That’s just over 1000 pixels per image, not too bad… and I bet we could still do an alright job.

![fit](pets-smol.png)


---

^
Except for Saucisse in the top-left… Like, that could be a cat… or a dog? I can’t really tell anymore.

![fit](pets-smol-dog.png)

---

^
The high-res versions are much more fun to look at…

^
Usually, you’d train a deep convolutional neural network, and hope that it learns some salient features that can be used to tell cats from dogs…

^
We’ve all got quality neural networks, let’s see if we can find some easy features to tell them apart…

^
(Usually, this would be the moment where there’s some crowd interaction… but, well, not all of you can give me direct feedback. Patrick, do you wanna have a go, and give me one difference between cats and dogs that we could use here?)

![fit](pets.png)

^
I think I have a simpler one… If there’s anything I know, it’s that dogs LOVE going for walks. So we’re probably more likely to see a dog out and about in nature… and thus… lotsa green!

---

^
And look! Lotsa green around Oki here! That’s good.

![fit](pets-green-1.png)

---

^
Unfortunately, Saucisse also loves going outside, so lotsa green there as well… But maybe we just need to add a second feature?

![fit](pets-green-2.png)

---

^
See, if there’s one thing I noticed, it’s that almost all cats have grey fur, but dogs NEVER do.

![fit](pets-grey.png)

---

^
So… Based on what we’ve seen, I feel fairly confident in saying that dogs have lotsa green, and very little grey.

![fit](pets.png)

[.text: #FFFFFF]

$$
\begin{array}{lrl}
\text{dog}(\hat{x}) & :=    & \text{lots_of_green}(\hat{x}) \\
                    & \land & \text{very_little_grey}(\hat{x})
\end{array}
$$

---

^
Let’s slap some axes on there, and would you look at that! They’re already in the right places!

^
It’s like I planned this.

^
Anyway, on the X-axis, we’ve got inverse greyness.

![fit](pets-plot.png)

---

^
Let’s abstract away a little, ’cuz technically those images are just points on this plot, and them being… really big… is gonna be a little confusing. So we’ve got this plot, now we’re gonna look for a function which can successfully tell cats from dogs…

![fit](abstract-1.png)

---

^
Let’s put a line… here! Everything to the right of that line is dogs!

![fit](abstract-2.png)

---

^
But if we now look at Oki, our dog, we see that if pick a point which is only a *tiny* step away, that’s already a cat. Mind you, we don’t have any images that correspond to this point, and we can’t visualise it, ’cuz we’ve reduced the complexity big a huge degree… All we know is its greenness and its ungreyness… We’re just working under the assumption that we’ve correctly identified the feature space in which cats and dogs are (linearly) seperable, and based on that assumption, if something is really close to a known dog… its probabbly still a dog!

![fit](abstract-3.png)

---

^
Okay, so let’s move our line a little…

![fit](abstract-4.png)

---

^
Now we’ve got the problem the other way around! Points that are REALLY close to Zaza are classified as dogs! What if we put a tiny green hat on her? Even the smallest bit of green can push the classifier into “dog” now!

![fit](abstract-5.png)

---

^
What if I put a tiny green hat on my cat? Does that look like a dog to you? It does to the classifier.

![left](zaza-with-hat.png)

# [fit] - Dog?

---

^
Okay, final move, we’re putting the line smack-dab in the middle… Now, if we take small steps from ANY known cat or dog, the classification remains the same…

![fit](abstract-6.png)

---

^
Let’s take stock:
- Base concepts, like “input data”, “features”, and “training”.
- You can extract features manually, like we did, but for deep neural networks, i.e., networks with multiple layers, the hope is that the first few layers learn to isolate the relevant features, and the last few layers perform classification based on those features.
- We’ve seen that neural networks are sneaky bastards. They don’t necessarily use the features you’d expect them to. Usually, this shows up because of flaws in your dataset, and this can have massive consequences.
- We’ve learned about adversarial examples—when I put a tiny green hat on my cat, to trick the network into classifying her as a dog, with minimal changes, and without changing how humans would classify her.
- We’ve seen robustness to adversarial examples—specifically, by measuring distance in the feature space.

# What have we seen so far?

---

^
So we’ve set the scene…

# What’s still to come?

---

^
So the data science that I’ve done in this talk so far was *terrible*, I hope you noticed. There’s a reason for that: We tend to think of verification, more or less, as a replacement for testing. You write down your specification, prove that your program follows it, and done! I don’t normally agree with that mindset, but it’s especially harmful here.

^
Verification is no replacement for good data science practices. It only helps you be sure the function you found follows your specification. (And remember, the quality of your specification is likely dependent on the quality of your data.)

[.column]

## Is our data good?

[.column]

## Did we find the right features?

[.column]

## Are we robust around these features?

---

^
However, for this talk, we’re only going to be talking about this very last issue.

^
Specifically, we’re approaching this problem from PL, and look for lightweight approaches to verifying robustness of neural nets.

[.column]

## **Is our data good?**

[.column]

## **Did we find the right features?**

[.column]

## *Are we robust around these features?*

---

^
We’re phrasing robustness as a refinement type.

^
We’re going to do that by talking about, e.g., the type of “images whose features are within some distance of a known cat.”

^
Recall, features are extracted from the data by neural networks, which are fairly constrained functions… they’re sequences of linear functions, alternated with non-linear activation functions (from a highly limited set).

# [fit] Robustness as a Refinement Type

---

^
Let’s get ourselves a classifier for our pet problem. The architecture we’re going with is VERY simple. It has two inputs (greenness and ungreyness), computes the linear function on the right-hand side, using weights w and bias b, and feeds the answer into the non-linear activation function f.

$$
\begin{array}{l}
\text{classify} : (x_1 \to \mathbb{R}) \to (x_2 \to \mathbb{R}) \to (y : \mathbb{R})\\
\text{classify} \; x_1 \; x_2 = f \; (w_1 x_1 + w_2 x_2 - b)\\
\end{array}
$$

---

^
Let’s fill in some weights, and an activation function.

^
S is the threshold function, which returns 1 if the input is positive, and 0 otherwise. It’s a real bad function to use in machine learning, ’cuz it’s not differentiable, but it’s intuitive… and we’re not gonna be differentiating things anyway.

^
Let’s check: 0.5 + 0.5 = 1, and 1 - 0.9 is 0.1, which gives us 1. Oki is still a dog. The cats are still cats.

$$
\begin{array}{l}
\text{classify} : (x_1 \to \mathbb{R}) \to (x_2 \to \mathbb{R}) \to (y : \mathbb{R})\\
\text{classify} \; x_1 \; x_2 = S \; (0.5 x_1 + 0.5 x_2 - 0.9)\\
\\
S \; x =
\begin{cases}
1, \; \text{if} \; x \geq 0 \\
0, \; \text{otherwise}
\end{cases}
\end{array}
$$

---

^
We’re using F\*, which has refinement types… So let’s translate this to F\*…

^
We’ve got a network, which is given by a matrix of weights, and a list of biases…

```fsharp
val model : network (*with*) 2 (*inputs*) 1 (*output*) 1 (*layer*)
let model = NLast // makes single-layer network
  { weights    = [[0.5R]; [0.5R]]
  ; biases     = [-0.9R]
  ; activation = Threshold
  }

val classify : (x1 : ℝ) → (x2 : ℝ) → (y : ℝ)
let classify = run model
```

---

^
Let’s write down our specification.

^
You can apply ‘doggy’ to either a greenness or an ungreyness value, and it will return true if it’s within doggy ranges… just happens to work for both features, since they happen to share the same range…

```fsharp

let ε = 0.1R

val doggy : (x : ℝ) → bool
let doggy x = 1.0R - ε ≤ x && x ≤ 1.0R + ε

val _ = (x1 : ℝ{doggy x1})
      → (x2 : ℝ{doggy x2})
      → (y  : ℝ{y = 1.0R})
val _ = classify
```

---

```lisp
(define-fun classify ((x1 Real) (x2 Real)) Real
  (ite (>= (- (+ (* x1 0.5) (* x2 0.5)) 0.9) 0.0) 1.0 0.0))
(define-fun doggy ((x Real)) Bool (and (<= 0.9 x) (<= x 1.1)))
(assert (forall ((x1 Real) (x2 Real))
  (=> (and (doggy x1) (doggy x2)) (= (classify x1 x2) 1.0))))
(check-sat)
```
